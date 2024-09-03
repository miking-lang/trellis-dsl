#include "cuda_runtime.h"
#include "device_launch_parameters.h"
#include "cuda.h"

#include "stdio.h"
#include "math.h"
#include "time.h"

#include "viterbi.h"

// New C++ inlcudes
#include <iostream>
#include <vector>
#include <string>
using namespace std;

// For dumping synchronized data to file
#include<H5Cpp.h>
using namespace H5;

// Global constants for max cuda device resources
constexpr unsigned int kMaxNumInstances = 64;
constexpr unsigned int kDurationTableMaxLength = 32;

// Non unser defined constants used for code maintainability
constexpr unsigned int kBitsPerBase = 2; // Normal value for 4 bases. May change to 3 for metylized bases
constexpr unsigned int kBaseNumber = 1 << kBitsPerBase;
constexpr unsigned int kBaseMask = kBaseNumber - 1;


namespace gpuDev
{

	/*

	CUDA Kernel constants

	*/

	// Cuda constants for kernels
	__constant__ unsigned int kNumInstances;
	__constant__ unsigned int kBatchLength;
	__constant__ unsigned int kBatchOverlap;
	__constant__ unsigned int kKmerMask;
	__constant__ unsigned int kCommonShift;
	__constant__ unsigned int kDurationShift;
	__constant__ unsigned int kDurationMask;
	__constant__ unsigned int kInstanceShift;
	__constant__ unsigned int kMaxDuration;
	__constant__ unsigned int kTotalStates;

	// Small lookup tables for kernel codes
	__constant__ float* observationCostTables[kMaxNumInstances];
	__constant__ unsigned int initializeationStates[kMaxNumInstances];
	__constant__ float durationCostTable[kDurationTableMaxLength];
	__constant__ float durationCostTail;

	/*

	CUDA Kernel functions

	*/

	// CUDA kernel for the Viterbi DNA decoder
	__global__
		void ViterbiPropagate(float* currentCost, unsigned int* tracebackState, const float* __restrict__ previousCost, const float* __restrict__ transitionCostTable) {

		const unsigned int thread = blockDim.x * blockIdx.x + threadIdx.x;
		const unsigned int currentLength = (thread >> kDurationShift)& kDurationMask;
		const unsigned int currentInstance = thread >> kInstanceShift;
		const unsigned int currentInstanceAdd = currentInstance << kInstanceShift;
		const unsigned int threadK = thread & kKmerMask; // Shuffle base indicies for contiguous L2 cache read of prior states
		const unsigned int currentKmer = (threadK >> kBitsPerBase) + ((threadK & kBaseMask) << kCommonShift);
		const unsigned int currentState = (currentLength << kDurationShift) + currentKmer;

		const float* __restrict__ observationCostTable = observationCostTables[currentInstance];

		if (observationCostTable == NULL) { // Code for when we have run out of signal to process...
			currentCost[currentState + currentInstanceAdd] = previousCost[currentState + currentInstanceAdd];
			tracebackState[currentState + currentInstanceAdd] = currentState;
			return;
		}

		unsigned int previousState, previousKmer, previousDuration, transitionPos;
		float bestCost, candidateCost;
		unsigned int bestPreviousState;

		// Continuation of the same K-mer
		if (currentLength >= (kMaxDuration - 1)) {
			previousDuration = currentLength;
			previousKmer = currentKmer;
			previousState = (previousDuration << kDurationShift) + previousKmer;
			candidateCost = previousCost[previousState + currentInstanceAdd] + durationCostTail;
		}
		else {
			previousDuration = currentLength + 1;
			previousKmer = currentKmer;
			previousState = (previousDuration << kDurationShift) + previousKmer;
			candidateCost = previousCost[previousState + currentInstanceAdd];
		}
		bestCost = candidateCost;
		bestPreviousState = previousState;

		// Possible new segment start from past K-mer state
		for (int n = 0; n < kBaseNumber; n++) {
			previousKmer = ((currentKmer << kBitsPerBase) & kKmerMask) + n;
			transitionPos = (currentKmer << kBitsPerBase) + n;
			previousDuration = 0; // Need to exit ended previous segment
			previousState = (previousDuration << kDurationShift) | previousKmer;
			//candidateCost = previousCost[previousState + currentInstanceAdd] + durationCostTable[currentLength] - 1.3863f; // Transition probability
			candidateCost = previousCost[previousState + currentInstanceAdd] + durationCostTable[currentLength] + transitionCostTable[transitionPos];
			if (candidateCost > bestCost) {
				bestCost = candidateCost;
				bestPreviousState = previousState;
			}
		}

		// Add cost of observation to state cost
		bestCost += observationCostTable[currentKmer];

		// Store cost and best previous state
		currentCost[currentState + currentInstanceAdd] = bestCost;
		tracebackState[currentState + currentInstanceAdd] = bestPreviousState;
	}

	// Initialize Viterbi costs for beginning of batch
	__global__
		void ViterbiInitialize(float* currentCost) {
		const unsigned int thread = blockDim.x * blockIdx.x + threadIdx.x;
		const unsigned int currentLength = (thread >> kDurationShift)& kDurationMask;
		const unsigned int currentInstance = thread >> kInstanceShift;
		const unsigned int currentKmer = thread & kKmerMask;
		const unsigned int currentState = (currentLength << kDurationShift) + currentKmer;

		const unsigned int initState = initializeationStates[currentInstance];

		if (initState == kTotalStates) { // Initialization for first batch of signal
			currentCost[thread] = 0;
		}
		else if (initState == currentState) // Cases for continuing batches
		{
			currentCost[thread] = 0;
		}
		else
		{
			currentCost[thread] = -INFINITY;
		}
	}

	// Inefficient non-parallel maximum state finder and Viterbi backtracker
	__global__
		void ViterbiBacktrack(unsigned int* optSequenceTable, const unsigned int* __restrict__ tracebackTable, const float* __restrict__ costTable) {

		const unsigned int thread = blockDim.x * blockIdx.x + threadIdx.x;
		const unsigned int currentInstance = thread; // Special case for Backtrack which rund with fewer threads

		const float* __restrict__ costs = costTable + currentInstance * kTotalStates;
		unsigned int* optSequence = optSequenceTable + currentInstance * kBatchLength;
		unsigned int state = 0;

		// Find maximum state
		float cost = costs[0];
		float mcost = cost;
		for (int s = 1; s < kTotalStates; s++) {
			cost = costs[s];
			if (cost > mcost) {
				mcost = cost;
				state = s;
			}
		}

		for (int m = kBatchLength - 1; m >= 0; m--) {
			optSequence[m] = state;
			const unsigned int* tracebackStates = tracebackTable + (currentInstance * kTotalStates) + m * (kTotalStates * kNumInstances);
			state = tracebackStates[state];
		}

	}


} // End namespace gpuDev

/*

Device handling C++ code

*/

class CUDAException : public exception {
	const char* what() const throw () {
		return "Something went wrong when interfacing with a cuda function...";
	}
};


ViterbiDevice::ViterbiDevice(const ViterbiDeviceParameters& Params)
{
	// Set constant parameters
	kNumInstances = Params.NumInstances;
	kKmerLength = Params.KmerLength;
	kSignalLevels = Params.SignalLevels;
	kBatchLength = Params.BatchLength;
	kBatchOverlap = Params.BatchOverlap;
	kThreadsPerBlock = 512; // Do this more elegantly
	kDurationBits = Params.DurationBits;

	// Derrived constants
	kTotalKmer = 1 << (kKmerLength * kBitsPerBase);
	kMaxDuration = 1 << kDurationBits;
	kTotalStates = kTotalKmer * kMaxDuration;

	// Set up constants for execution
	cudaMemcpyToSymbol(gpuDev::kNumInstances, &kNumInstances, sizeof(unsigned int), 0, cudaMemcpyHostToDevice);

	cudaMemcpyToSymbol(gpuDev::kBatchLength, &kBatchLength, sizeof(unsigned int), 0, cudaMemcpyHostToDevice);

	cudaMemcpyToSymbol(gpuDev::kBatchOverlap, &kBatchOverlap, sizeof(unsigned int), 0, cudaMemcpyHostToDevice);

	cudaMemcpyToSymbol(gpuDev::kMaxDuration, &kMaxDuration, sizeof(unsigned int), 0, cudaMemcpyHostToDevice);

	cudaMemcpyToSymbol(gpuDev::kTotalStates, &kTotalStates, sizeof(unsigned int), 0, cudaMemcpyHostToDevice);

	const unsigned int KmerLength = kKmerLength * kBitsPerBase;
	const unsigned int kKmerMask = (1 << KmerLength) - 1;
	cudaMemcpyToSymbol(gpuDev::kKmerMask, &kKmerMask, sizeof(unsigned int), 0, cudaMemcpyHostToDevice);

	const unsigned int kCommonShift = KmerLength - kBitsPerBase;
	cudaMemcpyToSymbol(gpuDev::kCommonShift, &kCommonShift, sizeof(unsigned int), 0, cudaMemcpyHostToDevice);

	const unsigned int kDurationShift = KmerLength;
	cudaMemcpyToSymbol(gpuDev::kDurationShift, &kDurationShift, sizeof(unsigned int), 0, cudaMemcpyHostToDevice);

	const unsigned int kDurationMask = kMaxDuration - 1;
	cudaMemcpyToSymbol(gpuDev::kDurationMask, &kDurationMask, sizeof(unsigned int), 0, cudaMemcpyHostToDevice);

	const unsigned int kInstanceShift = KmerLength + kDurationBits;
	cudaMemcpyToSymbol(gpuDev::kInstanceShift, &kInstanceShift, sizeof(unsigned int), 0, cudaMemcpyHostToDevice);

	// Cost tables
	cudaMemcpyToSymbol(gpuDev::durationCostTable, Params.ExplicitDurationTable, kMaxDuration * sizeof(float), 0, cudaMemcpyHostToDevice);
	cudaMemcpyToSymbol(gpuDev::durationCostTail, &(Params.DurationTailExponent), sizeof(float), 0, cudaMemcpyHostToDevice);

	try {
		cudaError_t status;

		// Allocate memory for woring buffers
		status = cudaMalloc(&CostMatrix, kNumInstances * kTotalStates * 2 * sizeof(float));
		if (status != cudaSuccess) throw CUDAException();

		status = cudaMalloc(&TracebackMatrix, kNumInstances * kTotalStates * kBatchLength * sizeof(unsigned int));
		if (status != cudaSuccess) throw CUDAException();

		status = cudaMalloc(&StateOutputBuffer, kNumInstances * kBatchLength * sizeof(unsigned int));
		if (status != cudaSuccess) throw CUDAException();

		// Allocate memory for tables
		status = cudaMalloc(&ObservationTable, kSignalLevels * kTotalStates * sizeof(float));
		if (status != cudaSuccess) throw CUDAException();

		status = cudaMalloc(&DurationTable, kMaxDuration * sizeof(float)); // Fix this for new konstants
		if (status != cudaSuccess) throw CUDAException();

		status = cudaMalloc(&TransitionTable, (kTotalStates << kBitsPerBase) * sizeof(float));
		if (status != cudaSuccess) throw CUDAException();

		// Copy Tables from host to GPU
		status = cudaMemcpy(ObservationTable, Params.ObservationTable, sizeof(float) * kSignalLevels * kTotalKmer, cudaMemcpyHostToDevice);
		if (status != cudaSuccess) throw CUDAException();

		status = cudaMemcpy(DurationTable, Params.ExplicitDurationTable, sizeof(float) * kMaxDuration, cudaMemcpyHostToDevice);
		if (status != cudaSuccess) throw CUDAException();

		status = cudaMemcpy(TransitionTable, Params.TransitionTable, sizeof(float) * (kTotalKmer << kBitsPerBase), cudaMemcpyHostToDevice);
		if (status != cudaSuccess) throw CUDAException();
	}

	// Should be changed to CUDA error event instead
	catch (CUDAException error) {
		cerr << "Was not able to set up CUDA device properly" << endl;

		// Deallocate memory before returning
		if (CostMatrix != NULL) {
			cudaFree(CostMatrix);
		}
		if (TracebackMatrix != NULL) {
			cudaFree(TracebackMatrix);
		}
		if (StateOutputBuffer != NULL) {
			cudaFree(StateOutputBuffer);
		}
		if (ObservationTable != NULL) {
			cudaFree(ObservationTable);
		}
		if (DurationTable != NULL) {
			cudaFree(DurationTable);
		}
		clog << "Cleaned up after cude setup error, rethrowing exception" << endl;
		throw std::move(error);
	}

	// Set up instances for data handling
	Instance.resize(kNumInstances);
	for (int n = 0; n < Instance.size(); n++) {
		Instance[n].SignalLength = 0;
		Instance[n].SignalPosition = 0;
		Instance[n].Signal.resize(0);
		Instance[n].StateOutput.resize(0);
	}

}

ViterbiDevice::~ViterbiDevice() {

	// Free memory on device
	cudaFree(CostMatrix);
	cudaFree(TracebackMatrix);
	cudaFree(StateOutputBuffer);
	cudaFree(ObservationTable);
	cudaFree(DurationTable);	

}

void ViterbiDevice::Initialize() {

	// Set up way to initizale starting buffer
	unsigned int initializeationStates[kMaxNumInstances];
	for (unsigned int n = 0; n < kNumInstances; n++) {
		if (Instance[n].SignalPosition == 0) {
			initializeationStates[n] = kTotalStates; // Control code to set all state costs to zero
		}
		else
		{
			unsigned int state = Instance[n].StateOutput[Instance[n].SignalPosition - 1];
			initializeationStates[n] = state; // Set cost of state to zero, and all else to -infinity
		}
	}
	cudaMemcpyToSymbolAsync(gpuDev::initializeationStates, initializeationStates, kNumInstances * sizeof(unsigned int), 0, cudaMemcpyHostToDevice, 0);

	// Initialize cost buffer
	float *currentPointer = CostMatrix + kNumInstances * kTotalStates;
	gpuDev::ViterbiInitialize <<< kNumInstances * kTotalStates / kThreadsPerBlock, kThreadsPerBlock, 0, 0 >>> (currentPointer);

	// Get ready to process batch
	BatchPosition = 0;
	CurrentBuffer = 0;
}

void ViterbiDevice::Propagate() {
	// Propagate Viterbi metric
	float* currentPointer;
	float* previousPointer;
	if (CurrentBuffer == 0) {
		currentPointer = CostMatrix;
		previousPointer = CostMatrix + kNumInstances * kTotalStates;
		CurrentBuffer = 1;
	}
	else {
		currentPointer = CostMatrix + kNumInstances * kTotalStates;
		previousPointer = CostMatrix;
		CurrentBuffer = 0;
	}
	unsigned int* tracebackPointer = TracebackMatrix + BatchPosition * kNumInstances * kTotalStates;
	float* observationCostTables[kMaxNumInstances];
	for (unsigned int n = 0; n < kNumInstances; n++) {
		if (Instance[n].SignalPosition + BatchPosition < Instance[n].SignalLength) {
			observationCostTables[n] = ObservationTable + kTotalKmer * Instance[n].Signal[Instance[n].SignalPosition + BatchPosition];
		}
		else
		{
			observationCostTables[n] = NULL;
		}
	}
	cudaMemcpyToSymbolAsync(gpuDev::observationCostTables, observationCostTables, kNumInstances * sizeof(float*), 0, cudaMemcpyHostToDevice, 0);
	gpuDev::ViterbiPropagate <<< kNumInstances * kTotalStates / kThreadsPerBlock, kThreadsPerBlock, 0, 0 >>> (currentPointer, tracebackPointer, previousPointer, TransitionTable);

	BatchPosition++; // Increment counter in batch
}

void ViterbiDevice::Backtrack() {
	// Fill state output buffer with optimal states
	float* costPosition;
	if (CurrentBuffer == 0) {
		costPosition = CostMatrix + kNumInstances * kTotalStates;
	}
	else {
		costPosition = CostMatrix;
	}
	gpuDev::ViterbiBacktrack <<< 1, kNumInstances , 0, 0 >>> (StateOutputBuffer, TracebackMatrix, costPosition);
}


void ViterbiDevice::Finalize() {

	for (int n = 0; n < Instance.size(); n++) {
		unsigned int copyLength;
		if (Instance[n].SignalPosition + kBatchLength > Instance[n].SignalLength) {
			copyLength = Instance[n].SignalLength - Instance[n].SignalPosition;
		}
		else
		{
			copyLength = kBatchLength - kBatchOverlap;
		}
		unsigned int* hostPointer = Instance[n].StateOutput.data() + Instance[n].SignalPosition;
		unsigned int* devicePointer = StateOutputBuffer + n * kBatchLength;
		cudaError_t status = cudaMemcpy(hostPointer, devicePointer, sizeof(unsigned int) * copyLength, cudaMemcpyDeviceToHost);
		if (status != cudaSuccess) cerr << "ERROR IN FINALIZE!!" << endl;

		Instance[n].SignalPosition += copyLength;
	}
}


void ViterbiDevice::ProcessBatch() {

	// Initialize the buffer
	Initialize();

	// Step through the Viterbi batches
	for (unsigned int n = 0; n < kBatchLength; n++) {
		Propagate();
	}

	// Backtrack through trellis to find optimal path
	Backtrack();

	// Wrap up execution and copy out memory
	Finalize();

	cudaDeviceSynchronize(); // Should maybe be places at the start

}


// Rudimentary data loader
void ViterbiDevice::LoadData(unsigned int n, Fast5Reader& Reader) {

	Reader.ReadSignal(Instance[n].Signal, Instance[n].RawData, Instance[n].Id);

	// Setup internal parameters
	Instance[n].SignalPosition = 0;
	unsigned int SignalLength = (unsigned int) Instance[n].Signal.size();
	Instance[n].SignalLength = SignalLength;
	Instance[n].StateOutput.resize(SignalLength);
}

// Rudimentary data. Should probably not even be in this part of the code
void ViterbiDevice::WriteData(unsigned int n) {

	// Write Signal ID to FastA file
	cout << ">" << Instance[n].Id.c_str() << endl;

	// Write decoded sequence
	char* dstr = (char*)"ACGT";
	unsigned int numprinted = 0;
	const unsigned int LengthShift = kKmerLength * kBitsPerBase;
	const unsigned int KMerMid = (kKmerLength >> 1) * kBitsPerBase; // Should really read this from model file
	for (unsigned int m = 0; m < Instance[n].SignalLength; m++) {
		unsigned int s = Instance[n].StateOutput[m];
		unsigned int x = (s >> KMerMid) & 0x03;
		if ((s >> LengthShift) == 0) {
			printf("%c", dstr[x]);
			numprinted++;
			TotalBasesDecoded++;
			if((numprinted % 80) == 0)
				printf("\n");
		}
	}
	if ((numprinted % 80) != 0) // Last part endl
		printf("\n");
}


// Rudimentary data dumber. Shoudl work with HDF5 file
void ViterbiDevice::WriteDataFull(std::string fname, unsigned int n) {

	volatile static bool first = true;

	// Size up the data
	int NumBases = 0; // Count the number of bases
	const unsigned int LengthShift = kKmerLength * kBitsPerBase;
	for (unsigned int m = 0; m < Instance[n].SignalLength; m++) {
		unsigned int s = Instance[n].StateOutput[m];
		if ((s >> LengthShift) == 0) {
			NumBases++;
		}
	}
	
	// Prepare the output
	vector<int16_t> Dacs; 
	vector<uint16_t> Reference;
	vector<uint32_t> Ref_to_signal;

	Reference.resize(NumBases);
	Ref_to_signal.resize(NumBases+1);
	Dacs = Instance[n].RawData; // Copy to new location for no real good reason

	Ref_to_signal[0] = 0; // Beginning of first base

	// Fill the output
	unsigned int numprinted = 0;
	const unsigned int KMerMid = (kKmerLength >> 1)* kBitsPerBase; // Should really read this from model file
	for (unsigned int m = 0; m < Instance[n].SignalLength; m++) {
		unsigned int s = Instance[n].StateOutput[m];
		unsigned int x = (s >> KMerMid) & 0x03;
		if ((s >> LengthShift) == 0) {
			Reference[numprinted] = (uint16_t) x;
			Ref_to_signal[numprinted+1] = m+1;
			numprinted++;
			TotalBasesDecoded++;
		}
	}

	try {
		// Open HDF5 file to save signal
		int acc;
		if (first) acc = H5F_ACC_TRUNC;
		else acc = H5F_ACC_RDWR;
		H5File file(fname, acc); // Ugly soulution, but better than noting

		// Create reads group only if nessessary
		if (first) file.createGroup("/Reads");
		Group reads(file.openGroup("/Reads"));

		// Do not create new file or Reads group next time
		first = false;

		Group read(reads.createGroup(Instance[n].Id)); // Create group with read name

		{ // Write Dacs data
			hsize_t dims[1];
			dims[0] = Dacs.size();
			DataSpace dspace(1, dims);
			DataSet data = read.createDataSet("Dacs", PredType::STD_I16LE, dspace);
			data.write((void *) &(Dacs[0]), PredType::STD_I16LE);
		}

		{ // Write Reference data
			hsize_t dims[1];
			dims[0] = Reference.size();
			DataSpace dspace(1, dims);
			DataSet data = read.createDataSet("Reference", PredType::STD_I16LE, dspace);
			data.write((void*)&(Reference[0]), PredType::STD_I16LE);
		}

		{ // Write Ref_to_signal
			hsize_t dims[1];
			dims[0] = Ref_to_signal.size();
			DataSpace dspace(1, dims);
			DataSet data = read.createDataSet("Ref_to_signal", PredType::STD_I32LE, dspace);
			data.write((void*)&(Ref_to_signal[0]), PredType::STD_I32LE);
		}

	}
	catch (const H5::FileIException) {
		cerr << "ERROR: unable to save called data to '" << fname << "'" << endl;
		exit(1);
	}
	catch (const H5::Exception) {
		cerr << "ERROR: unable to save called data to '" << fname << "'" << endl;
		exit(1);
	}
}

unsigned int ViterbiDevice::NumInstances() const
{
	return (unsigned int) Instance.size();
}


bool ViterbiDevice::InstanceIdle(unsigned int instance) const
{
	return Instance[instance].SignalPosition >= Instance[instance].SignalLength;
}

bool ViterbiDevice::AllIdle() const
{
	bool allidle = true;
	for (unsigned int i = 0; i < kNumInstances; i++) {
		if (InstanceIdle(i) == false) allidle = false;
	}
	return allidle;
}

bool ViterbiDevice::InstanceFinished(unsigned int instance) const
{
	if ((Instance[instance].SignalPosition >= Instance[instance].SignalLength) && (Instance[instance].SignalLength > 0))
		return true;
	else
		return false;
}

int
GetDeviceCount() {
	int count;
	cudaError_t status = cudaGetDeviceCount(&count);
	if (status != cudaSuccess) throw CUDAException();

	return count;
}

void
SetActiveDevice(int device) {
	cudaError_t status = cudaSetDevice(device);
	if (status != cudaSuccess) throw CUDAException();
}