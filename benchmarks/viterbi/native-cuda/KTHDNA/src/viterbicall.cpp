
#include "stdio.h"
#include "math.h"

#include "viterbi.h"
#include "model.h"
#include "fast5reader.h"
#include "signal.h"
// Argument parsing
#include<boost/program_options.hpp>
namespace po = boost::program_options;

#include <iostream>
#include <vector>
#include <string>
#include <chrono>
using namespace std;
using namespace std::chrono;

// Current version of the program
constexpr auto kVersionString = "0.95";

// File to write mapped reads to
std::string mapped_fname;

/*

The main controller code

*/

// Main controller code that does all of the work
void ViterbiBaseCaller(const string &model, const vector<string> &inputs, int parallel, int batchsize, int batchoverlap) {

	// Read the model from HDF5 file (should be build into the decoder)
	ViterbiModel Model(model);
	Model.Logarithmic(); // Needed for Viterbi algorithm

	// Read list of signals into reader object
	Fast5Reader Reader(inputs, Model);

	// Initialise and allocate memory as needed

	// Create one (or more) Device(s) with some Viterbi instances

	ViterbiDeviceParameters DeviceParams;
	DeviceParams.KmerLength = Model.KmerLength;
	DeviceParams.SignalLevels = Model.SignalLevels;
	DeviceParams.BatchLength = batchsize;
	DeviceParams.BatchOverlap = batchoverlap;
	DeviceParams.NumInstances = parallel;
	DeviceParams.DurationBits = Model.DurationBits;

	DeviceParams.ObservationTable = Model.ObservationTable;
	DeviceParams.ExplicitDurationTable = Model.ExplicitDurationTable;
	DeviceParams.TransitionTable = Model.TransitionTable;
	DeviceParams.DurationTailExponent = Model.DurationTailExponent;

	ViterbiDevice Device(DeviceParams); // Allocated memory needed for the device (Fix this to avoid all the extra parameters)

	duration<double> time_span(0.0);
	duration<double> ltime_span(0.0);

	high_resolution_clock::time_point t1 = high_resolution_clock::now();

	bool WorkToDo = true;

	while (WorkToDo) {

		// See if there is data to fetch
		high_resolution_clock::time_point lt1 = high_resolution_clock::now();
		for (unsigned int i=0; i < Device.NumInstances(); i++) {
			if (Device.InstanceIdle(i)) {
				Device.LoadData(i, Reader);
			}
		}
		high_resolution_clock::time_point lt2 = high_resolution_clock::now();
		ltime_span += duration_cast<duration<double>>(lt2 - lt1);

		if (Device.AllIdle()) {
			WorkToDo = false;
		}
		else {
			Device.ProcessBatch();
		}

		// See if there is finished data to push
		for (unsigned int i = 0; i < Device.NumInstances(); i++) {
			if (Device.InstanceFinished(i)) {
				if (mapped_fname.size() > 0) {
					Device.WriteDataFull(mapped_fname, i);
				}
				else {
					Device.WriteData(i);
				}
			}
		}

	}

	high_resolution_clock::time_point t2 = high_resolution_clock::now();
	time_span = duration_cast<duration<double>>(t2 - t1);

	clog << "Timing information..." << endl;
	clog << "Decoding execution time : " << time_span.count() << " s" << endl;
	clog << "Loading time : " << ltime_span.count() << " s" << endl;
	clog << "Number of bases : " << Device.TotalBasesDecoded << endl;
	clog << "Bases per second : " << Device.TotalBasesDecoded / time_span.count() << endl;

}

/*

The main function

*/

int main(int argc, char** argv) {

	// Declare program options
	po::options_description generic("Generic");
	generic.add_options()
		("help", "Print this help message.")
		("version", "Print the version string.")
		("verbose,v", "Print evaluation information to clog.");

	po::options_description config("Program configuration");
	config.add_options()
		("model,m", po::value<string>(), "Specifies model file to use.")
		("mapped", po::value<string>(), "Output file (hdf5) for mapped basecalls.")
		("parallelism,p", po::value<int>()->default_value(1), "Number of parallel Viterbi instances.")
		("batch-size", po::value<int>()->default_value(1024), "Size of sample batch in Viterbi.")
		("batch-overlap", po::value<int>()->default_value(128), "Overlap of sample batches.")
		("pure", po::bool_switch()->default_value(false), "Pure mode - do not rescale the raw data samples")	  
		("gpudevice,d", po::value<int>()->default_value(0), "GPU device to use.");


	po::options_description hidden("Hidden options");
	hidden.add_options()
		("input", po::value< vector<string> >(), "input");
	po::positional_options_description p;
	p.add("input", -1);

	po::options_description all_options;
	all_options.add(generic).add(config).add(hidden);

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

	// Retrive vector of fast5 input files or directories
	if (vm.count("input") == 0) {
		cerr << "ERROR: no fast5 input files or directories specified" << endl;
		return 1;
	}
	vector<string> inputs = vm["input"].as< vector<string> >();

	// Obtain model file
	if (vm.count("model") == 0) {
		cerr << "ERROR: no model file specified, see --model option" << endl;
		return 1;
	}
	string model = vm["model"].as< string >();

	// Set output file if provided
	if (vm.count("mapped") == 1) {
		mapped_fname = vm["mapped"].as< string >();
	};

	int parallel = vm["parallelism"].as< int >();
	if (parallel < 1) {
		cerr << "ERROR: option -p [--parallelism] used with argument less than 1" << endl;
		return 1;
	}

	int batchsize = vm["batch-size"].as< int >();
	if (batchsize < 2) {
		cerr << "ERROR: option '--batch-size' must be at least 2" << endl;
		return 1;
	}

	int batchoverlap = vm["batch-overlap"].as< int >();
	if (batchoverlap >= batchsize) {
		cerr << "ERROR: option '--batch-overlap' must be strictly smaller than '--batch-size'" << endl;
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
	// Set active GPU device
	int device = vm["gpudevice"].as< int >();
	int numdev = GetDeviceCount();
	if ((device < 0) || (device >= numdev)) {
		cerr << "ERROR: Must chose GPU device number between 0 and numDevices-1" << endl;
		exit(1);
	}
	SetActiveDevice(device);
	clog << "Using GPU device " << device << " out of " << numdev << " available" << endl;

	// This is where the magic happens
	// Call the main code here
	ViterbiBaseCaller(model, inputs, parallel, batchsize, batchoverlap);

	// Wait for window (not in production code)
	// cin.get();

	// And we are done
	return 0;
}
