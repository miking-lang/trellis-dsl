// ViterbiTrain.cpp : This file contains the 'main' function. Program execution begins and ends there.
//


#include <iostream>
#include <vector>
#include <math.h>
#include <chrono>
using namespace std;
using namespace std::chrono;

#include "H5Cpp.h"
using namespace H5;

// Argument parsing
#include<boost/program_options.hpp>
namespace po = boost::program_options;

#include "model.h"
#include "model.h"
#include "stdio.h"

#include "baumwelch.h"
#include "signal.h"

// Current version of the program
constexpr auto kVersionString = "0.95";

// Model parameters
constexpr unsigned int NumInstances = 512; // Size of duration state variable

// Mixed constants (to be changed once we integrate with gpu code)
constexpr unsigned int WindowLength = 32;
constexpr unsigned int WindowCenter = 16;
constexpr unsigned int BlockLength = 1024;

// Data from the file
vector<int16_t> Dacs;
vector<uint16_t> Reference;
vector<uint32_t> Ref_to_signal;
vector<int16_t> Medians;
vector<uint16_t> Deviations;

// Processed data
vector<unsigned int> Signal;
vector<uint32_t> Signal_to_ref;
vector<uint32_t> Kmers;

unsigned int MaxMem = 0;

float *NewObservationTable;
float *NewDurationTable;

// Dynamically allocated buffers for new model
float *BranchBufferRDebug; // This one is needed if we should update the branch probabilities)
float *ObservationTableDebug;
float* FitBufferDebug; // Fitness metric
float* GammaBufferDebug;

// Measure average fitness values
double FitnessSum = 0.0;
int FitnessCount = 0;

// User parameters to be used in training
string input_file;
string output_file;
string mapped_reads_file;
int NumIterations = 0;
bool UpdateObservation = false;
bool UpdateDuration = false;
bool HardDecoding = false;

// Temporary debug code
void
SaveFData(const string& model, const float* data, unsigned int rows, unsigned int columns) {

	try {
		// Open HDF5 file to save model
		H5File file(model, H5F_ACC_TRUNC);

		hsize_t dims[2];
		dims[0] = columns;
		dims[1] = rows;
		DataSpace dataspace(2, dims);
		DataSet dataset = file.createDataSet("/Data", PredType::IEEE_F32LE, dataspace);
		dataset.write(data, PredType::IEEE_F32LE);
	}
	catch (const H5::Exception) {
		cerr << "ERROR: something went wrong with saving '" << model << "'" << endl;
	}
}



// Assumes vectors Kmers (to be renamed KmerReference), Signal, and Signal_to_ref

void
AllocateBufferMemory(ViterbiModel& Model) {
	// Quick fix for now. Clean this up later
	unsigned int KmerSize = Model.KmerLength;
	unsigned int TotalKmers = 1 << (2 * KmerSize);
	unsigned int DurationLength = Model.DurationLength;
	unsigned int SignalLevels = Model.SignalLevels;

	// Allocate needed memory
	NewObservationTable = new float[TotalKmers * SignalLevels];
	NewDurationTable = new float[2 * DurationLength];

	BranchBufferRDebug = new float[2 * DurationLength]; // This one is needed if we should update the branch probabilities)
	ObservationTableDebug = new float[(1 << (2 * KmerSize)) * SignalLevels]; // This one is needed if we 
	FitBufferDebug = new float[NumInstances];
	GammaBufferDebug = new float[WindowLength * BlockLength * NumInstances];
}



// Keep track of which instance ie being loaded at the moment
static int CurrentInstance = 0;

void
ForwardBackwardBlockGPU(ViterbiModel &Model, int BlockStart) {
	// Quick fix for now. Clean this up later
	unsigned int KmerSize = Model.KmerLength;
	unsigned int TotalKmers = 1 << (2 * KmerSize);

	// Store observation probabilities
	static float ObservationBuffer[WindowLength * BlockLength * NumInstances];
	static unsigned int KmerBuffer[WindowLength * BlockLength * NumInstances];
	static unsigned int SignalBuffer[BlockLength * NumInstances];
	static int StateShiftBuffer[BlockLength * NumInstances];
	int reference_length = (int) Kmers.size();

	// Fill observation buffer for decoding
	for (int m = 0; m < BlockLength; m++) {
		int reference_base_position = (int)Signal_to_ref[m + BlockStart];
		unsigned int signal_value = Signal[m + BlockStart];
		SignalBuffer[CurrentInstance + m * NumInstances] = signal_value;
		float* observation_table = Model.ObservationTable + signal_value * TotalKmers;
		for (int n = 0; n < WindowLength; n++) {
			int reference_position = reference_base_position + n - WindowCenter;
			if ((reference_position >= 0) && (reference_position < reference_length) && (n > 0) && (n < (WindowLength - 1))) { // Position is within reference signal window
				unsigned int kmer = Kmers[reference_position];
				ObservationBuffer[n + CurrentInstance * WindowLength + m * WindowLength * NumInstances] = observation_table[kmer];
				KmerBuffer[n + CurrentInstance * WindowLength + m * WindowLength * NumInstances] = kmer;
			}
			else {
				ObservationBuffer[n + CurrentInstance * WindowLength + m * WindowLength * NumInstances] = 0.0f;
				KmerBuffer[n + CurrentInstance * WindowLength + m * WindowLength * NumInstances] = 0; // Dummy value that should not be assigned any values anyway
			}
		}
	}
	// Fill state shift buffer
	for (int m = 0; m < BlockLength; m++) {
		if (m + BlockStart > 0) {
			if (Signal_to_ref[m + BlockStart] > Signal_to_ref[m + BlockStart - 1]) {
				StateShiftBuffer[CurrentInstance + m * NumInstances] = 1;
			}
			else
			{
				StateShiftBuffer[CurrentInstance + m * NumInstances] = 0;
			}
		}
		else {
			StateShiftBuffer[CurrentInstance + m * NumInstances] = 0;
		}
	}
	
	// Jump to GPU code here if ready
	CurrentInstance++;
	if (CurrentInstance == NumInstances) {
		if (HardDecoding == false) {
			// Forward backward soft decoding
			GPUAlphaBetaCompute(Model, ObservationBuffer, KmerBuffer, SignalBuffer, StateShiftBuffer);

			// Check fitness values
			for (int i = 0; i < NumInstances; i++) {
				FitnessCount++;
				FitnessSum += (double)FitBufferDebug[i];
			}
		}
		else {
			// Viterbi based hard decoding
			GPUViterbiCompute(Model, ObservationBuffer, KmerBuffer, SignalBuffer, StateShiftBuffer);
		}
		CurrentInstance = 0;
	}
}

void
PrepareObservations(ViterbiModel& Model) {
	// Quick fix for now. Clean this up later
	unsigned int KmerSize = Model.KmerLength;
	unsigned int TotalKmers = 1 << (2 * KmerSize);
	unsigned int SignalLevels = Model.SignalLevels;

	for (unsigned int kmer = 0; kmer < TotalKmers; kmer++) {
		for (unsigned int sval = 0; sval < SignalLevels; sval++) {
			NewObservationTable[kmer + sval * TotalKmers] = 0.0f;
		}
	}
}

void
FinalizeObservationsGPU(ViterbiModel& Model) {
	// Quick fix for now. Clean this up later
	unsigned int KmerSize = Model.KmerLength;
	unsigned int TotalKmers = 1 << (2 * KmerSize);
	unsigned int SignalLevels = Model.SignalLevels;

	// Normalize observations (and write to table)
	for (unsigned int kmer = 0; kmer < TotalKmers; kmer++) {
		float sum = 0.0f;
		for (unsigned int sval = 0; sval < SignalLevels; sval++) {
			sum += ObservationTableDebug[kmer + sval * TotalKmers];
		}
		for (unsigned int sval = 0; sval < SignalLevels; sval++) {
			Model.ObservationTable[kmer + sval * TotalKmers] = 1e-8 + (1-1e-8) * ObservationTableDebug[kmer + sval * TotalKmers] / sum;
		}
	}
}

void
PrepareDurations(ViterbiModel& Model) {
	// Quick fix for now. Clean this up later
	unsigned int DurationLength = Model.DurationLength;

	for (unsigned int d = 0; d < 2 * DurationLength; d++) {
		NewDurationTable[d] = 0.0f;
	}
}

void
FinalizeDurationsGPU(ViterbiModel& Model) {
	// Quick fix for now. Clean this up later
	unsigned int DurationLength = Model.DurationLength;

	float sum = 0.0;
	for (unsigned int d = 0; d < DurationLength; d++) {
		sum += BranchBufferRDebug[d];
	}
	for (unsigned int d = 0; d < DurationLength; d++) {
		Model.ExplicitDurationTable[d] = BranchBufferRDebug[d] / sum;
	}
	sum = BranchBufferRDebug[2 * DurationLength - 1] + BranchBufferRDebug[2 * DurationLength - 2];
	float TailFactor = BranchBufferRDebug[2 * DurationLength - 1] / sum;
	Model.TailFactor = TailFactor;
}

void
MakeDurationsLogConcave(ViterbiModel& Model) {

	int DurationLength = Model.DurationLength;
	float* DurationTable = Model.ExplicitDurationTable;
	float TailFactor = Model.TailFactor;
	float DurationTailExponent = log(TailFactor);

	// Move into logatithmic domain
	DurationTable[DurationLength - 1] *= (1 - TailFactor);
	for (int d = 0; d < DurationLength; d++) {
		DurationTable[d] = log(DurationTable[d]);
	}

	// Move points up to make distribution Log concave
	for(int a=0; a < DurationLength - 2; a++) {
		for (int b = a + 2; b < DurationLength; b++) {
			for (int c = a + 1; c < b; c++) {
				float pa = DurationTable[a];
				float pb = DurationTable[b];
				float pc = ((float)(b - c) * pa + (float)(c - a) * pb) / (float)(b - a);
				if (DurationTable[c] < pc) {
					DurationTable[c] = pc;
				}
			}
		}
	}

	// Set tail exponent
	float newDurationTailExponent = DurationTable[DurationLength - 1] - DurationTable[DurationLength - 2];
	if (newDurationTailExponent < DurationTailExponent) DurationTailExponent = newDurationTailExponent;


	// Move back into linear domain
	for (int d = 0; d < DurationLength; d++) {
		DurationTable[d] = exp(DurationTable[d]);
	}
	TailFactor = exp(DurationTailExponent);
	DurationTable[DurationLength - 1] /= (1 - TailFactor);

	// Renormalize to ge a proper probability distribution
	float sum = 0.0f;
	for (int d = 0; d < DurationLength; d++) {
		sum += DurationTable[d];
	}
	for (int d = 0; d < DurationLength; d++) {
		DurationTable[d] /= sum;
	}

	// Write back to model
	Model.TailFactor = TailFactor;
	Model.DurationTailExponent = DurationTailExponent;

}

int PreviosProgress = -1;

void
ProgressIndicator(float progress) {

	int barWidth = 60;
	int pos = (int) ((float) barWidth) * progress;
	if(int(progress * 100.0) != PreviosProgress) {
		std::cout << "[";
		for (int i = 0; i < barWidth; ++i) {
			if (i < pos) std::cout << "=";
			else if (i == pos) std::cout << ">";
			else std::cout << " ";
		}
		std::cout << "] " << int(progress * 100.0) << " %\r";
		std::cout.flush();
		
		PreviosProgress = int(progress * 100.0);
	}
}

void
ProgressIndicatorFinish() {

	int barWidth = 60;
	std::cout << "[";
	for (int i = 0; i < barWidth; ++i) {
		std::cout << "=";
	}
	std::cout << "] " << int(100.0) << " %\n";
	std::cout.flush();

	PreviosProgress = -1;
}



// Debug counters
double NumSamples = 0;
double NumBases = 0;

// Create list of reads to use for training

vector<string> reads_list;

herr_t
file_info(hid_t loc_id, const char* name, const H5L_info_t* linfo, void* opdata)
{
	reads_list.push_back(name);
	return 0;
}

void
BuildReadList() {
	H5File file(mapped_reads_file, H5F_ACC_RDONLY);
	Group reads = file.openGroup("/Reads");
	herr_t idx = H5Literate(reads.getId(), H5_INDEX_NAME, H5_ITER_INC, NULL, file_info, NULL);
}


void
ProcessTrainingData(ViterbiModel &Model) {

	// Quick fix for now. Clean this up later
	unsigned int KmerSize = Model.KmerLength;
	unsigned int TotalKmers = 1 << (2 * KmerSize);

	duration<double> ltime_span(0.0);
	duration<double> ntime_span(0.0);
	//duration<double> nmtime_span(0.0);
	duration<double> ptime_span(0.0);
	high_resolution_clock::time_point t1, t2;
	//high_resolution_clock::time_point t1n, t2n;


	// Prepare working buffers
	PrepareObservations(Model);
	PrepareDurations(Model);

	// Setup for new run
	CurrentInstance = 0;

	// Setup GPU
	GPUSetup(Model);

	// Open file
	H5File file(mapped_reads_file, H5F_ACC_RDONLY);
	Group reads = file.openGroup("/Reads");

	//hsize_t numReads = reads.getNumObjs();
	int numReads = reads_list.size(); // Faster code
	cout << "Number of reads: " << numReads << endl;

	// *** Test to iterate over object in root directory
	//cout << endl << "Iterating over elements in the file" << endl;
	//herr_t idx = H5Literate(reads.getId(), H5_INDEX_NAME, H5_ITER_INC, NULL, file_info, NULL);
	//cout << endl;

	// Set up fitness measurements
	FitnessCount = 0;
	FitnessSum = 0.0;

	// Loop through reads
	for (hsize_t readId = 0; readId < numReads; readId++) {
	//{
		//hsize_t readId = 2;

		//cout << "Processing read nr : " << readId << endl;
		ProgressIndicator((float)readId / numReads);

		// Obtain read name for first read the training data file
		//t1n = high_resolution_clock::now();
		//H5std_string readName = reads.getObjnameByIdx(readId);
		H5std_string readName = reads_list[readId];
		//t2n = high_resolution_clock::now();
		//nmtime_span += duration_cast<duration<double>>(t2n - t1n);
		t1 = high_resolution_clock::now();
		Group read = reads.openGroup(readName);
		//cout << "Read name : " << readName << endl;

		// Get the data relevant for the read
		{
			// Open Dacs data set
			DataSet dataset = read.openDataSet("Dacs");
			DataSpace dataspace = dataset.getSpace();

			hsize_t dims;
			dataspace.getSimpleExtentDims(&dims, NULL);
			//cout << "Length: " << dims << endl;

			Dacs.resize(dims);
			dataset.read(Dacs.data(), PredType::STD_I16LE);
		}

		{
			// Open Reference data set
			DataSet dataset = read.openDataSet("Reference");
			DataSpace dataspace = dataset.getSpace();

			hsize_t dims;
			dataspace.getSimpleExtentDims(&dims, NULL);
			//cout << "Length: " << dims << endl;

			Reference.resize(dims);
			dataset.read(Reference.data(), PredType::STD_I16LE);
		}

		{
			// Open Dacs data set
			DataSet dataset = read.openDataSet("Ref_to_signal");
			DataSpace dataspace = dataset.getSpace();

			hsize_t dims;
			dataspace.getSimpleExtentDims(&dims, NULL);
			//cout << "Length: " << dims << endl;

			Ref_to_signal.resize(dims);
			dataset.read(Ref_to_signal.data(), PredType::STD_I32LE);
		}

		t2 = high_resolution_clock::now();
		ltime_span += duration_cast<duration<double>>(t2 - t1);

		// Normalize the data
		t1 = high_resolution_clock::now();

		unsigned int RawSize = (unsigned int)Dacs.size();
		unsigned int RefSize = (unsigned int)Reference.size();

		// Part of signal that is useful
		unsigned int KmerPrefixSize = (KmerSize >> 1);
		unsigned int KmerPostfixSize = (KmerSize >> 1)+1; // Allow one to estimate the Kmer transition probabilities as well (add one)

		unsigned int SignalStart = (unsigned int) Ref_to_signal[KmerPrefixSize];
		unsigned int SignalEnd = (unsigned int) Ref_to_signal[RefSize - KmerPostfixSize];

		// Normalize the full Dacs signal
		Signal::Normalize(Signal, Dacs, 8192*8, Model.SignalLevels, Model.LowClip, Model.HighClip);
		//SaveSData("Signal.hd5", Signal.data(), Signal.size());

		// Not dependent on signal start or end...
		// Prepate k-mer values from reference
		unsigned int KmerRefSize = RefSize - KmerPrefixSize - KmerPostfixSize;
		Kmers.resize(KmerRefSize);
		for (unsigned int n = 0; n < KmerRefSize; n++) {
			unsigned int kmer = 0;
			for (unsigned int k = 0; k < KmerSize; k++) {
				kmer += Reference[n + k] << (2 * k); // Build k-mer
			}
			Kmers[n] = kmer;
		}

		// Create backward pointer from signal to position in reference
		Signal_to_ref.resize(RawSize);
		for (unsigned int n = 0; n < KmerRefSize; n++) {
			unsigned int SegmentStart = Ref_to_signal[n + KmerPrefixSize];
			unsigned int SegmentEnd = Ref_to_signal[n + KmerPrefixSize + 1];
			for (unsigned int m = SegmentStart; m < SegmentEnd; m++) {
				Signal_to_ref[m] = n;
			}
		}
		
		t2 = high_resolution_clock::now();
		ntime_span += duration_cast<duration<double>>(t2 - t1);

		// Do we actually need the safety margin here???
		t1 = high_resolution_clock::now();
		for (unsigned int bs = SignalStart; bs < (SignalEnd - BlockLength); bs += BlockLength) {
			ForwardBackwardBlockGPU(Model, bs); // GPU code (produce debug output)
		}
		t2 = high_resolution_clock::now();

		//t2 = high_resolution_clock::now();
		ptime_span += duration_cast<duration<double>>(t2 - t1);

	}

	//cout << endl; // Just jump over the status bar
	ProgressIndicatorFinish();

	// Display average data fitness
	clog << "Average block data log likelihood : " << FitnessSum / (double)FitnessCount << endl;

	// Old stuff from CPU computation
	if (UpdateObservation) {
		FinalizeObservationsGPU(Model);
		clog << "Updated observation probabilites" << endl;
	}
	if (UpdateDuration) { // Should we update the duations
		FinalizeDurationsGPU(Model);
		//MakeDurationsLogConcave(Model);
		clog << "Updated duration probabilites" << endl;
	}

	// Clean up on GPU
	GPUCleanup();

	//clog << "Name lookup time : " << nmtime_span.count() << " s" << endl;
	clog << "Load time : " << ltime_span.count() << " s" << endl;
	clog << "Normalization time : " << ntime_span.count() << " s" << endl;
	clog << "Processing (and debugging) time : " << ptime_span.count() << " s" << endl;
}


// Train a full model from scatch
void FullTrain() {

	// Load the model to improve
	ViterbiModel Model(input_file);

	// Get memory to be able to update model
	AllocateBufferMemory(Model);

	// Build list of read names
	duration<double> time_span(0.0);
	high_resolution_clock::time_point t1, t2;
	clog << "Building reads list" << endl;
	t1 = high_resolution_clock::now();
	BuildReadList();
	t2 = high_resolution_clock::now();
	time_span += duration_cast<duration<double>>(t2 - t1);
	clog << "Completed in : " << time_span.count() << " s" << endl;
	
	clog << "Beginning training..." << endl;
	// Iterate
	for (int i = 0; i < NumIterations; i++) {
		// Go through training data to build a new model
		cout << "Baum Welch iteration " << i + 1 << endl;
		ProcessTrainingData(Model);
	}

	// Save the model after training
	Model.SaveModel(output_file);
}


int main(int argc, char** argv)
{
	// Parse input arguments here
	// Declare program options
	po::options_description generic("Generic");
	generic.add_options()
		("help", "Print this help message.")
		("version", "Print the version string.");

	po::options_description config("Program configuration");
	config.add_options()
		("input,i", po::value<string>(), "Specifies the input model file.")
		("output,o", po::value<string>(), "Specifies the output model file.")
		("mapped,m", po::value<string>(), "Mapped reads file (hdf5) to use for training.")
		("iterations,I", po::value<int>()->default_value(10), "Number of iterations.")
		("gpudevice,d", po::value<int>()->default_value(0), "GPU device to use.")
		("pure", po::bool_switch()->default_value(false), "Pure mode - do not rescale the raw data samples")	  
		("mode,M", po::value<int>()->default_value(1), "Update mode, 1=only observation, 2=only duration, 3=both durations and observations")
		("hard,H", po::bool_switch()->default_value(false), "Hard (Viterbi) matching of reference to signal samples");

	po::positional_options_description p;

	po::options_description all_options;
	all_options.add(generic).add(config);

	po::options_description visible_options("Options");
	visible_options.add(generic).add(config);

	// Parse program input
	po::variables_map vm;
	try {
		po::store(po::command_line_parser(argc, argv).options(all_options).positional(p).run(), vm);
		po::notify(vm);
	}
	catch (po::error & e)
	{
		cerr << "ERROR: " << e.what() << endl;
		return 1;
	}

	// Deal with query type options
	if (vm.count("help")) {
		clog << visible_options << endl;
		return 1;
	}
	if (vm.count("version")) {
		clog << "Version : " << kVersionString << endl; // Change to clog later
		return 1;
	}

	// Parameter handling and high level error checking

	// Retrive input file name
	if (vm.count("input") != 1) {
		cerr << "ERROR: need to specify one input file" << endl;
		return 1;
	}
	input_file = vm["input"].as< string >();

	// Retrive output file name
	if (vm.count("output") != 1) {
		cerr << "ERROR: need to specify one output file" << endl;
		return 1;
	}
	output_file = vm["output"].as< string >();

	// Retrive mapped reads file name
	if (vm.count("mapped") != 1) {
		cerr << "ERROR: need to specify one mapped reads file" << endl;
		return 1;
	}
	mapped_reads_file = vm["mapped"].as< string >();

	// Get numerical options
	NumIterations = vm["iterations"].as< int >();
	if (NumIterations < 1) {
		cerr << "ERROR: option -I [--iterations] used with argument less than 1" << endl;
		return 1;
	}
	// Switch normalization scheme depending on context
	if (vm["pure"].as< bool >()) {
		Signal::NormalizationMethod = 0;
	}
	else
	{
		Signal::NormalizationMethod = 1;
	}
	// Decide what to update
	int mode = vm["mode"].as< int >();
	if ((mode < 0) || (mode > 3)) {
		cerr << "ERROR: Mode must be a value between 0 and 3" << endl;
		exit(1);
	}
	UpdateObservation = ((mode & 0x01) > 0);
	UpdateDuration = ((mode & 0x02) > 0);

	// Switch to ude hard decoding
	HardDecoding = vm["hard"].as< bool >();
	if (HardDecoding && UpdateDuration) {
		cerr << "Duration updates not yet supported for hard decoding" << endl;
		exit(-1);
	}

	// Set active GPU device
	int device = vm["gpudevice"].as< int >();
	int numdev = GetDeviceCount();
	if ((device < 0) || (device >= numdev)) {
		cerr << "ERROR: Must chose GPU device number between 0 and numDevices-1" << endl;
		exit(1);
	}
	SetActiveDevice(device);
	clog << "Using GPU device " << device << " out of " << numdev << " available" << endl;

	// Train the model
	FullTrain();

}
