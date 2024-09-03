#pragma once

#include <vector>
#include <string>

#include "fast5reader.h"

// Find more elegant fix for this
#include<H5Cpp.h>

struct ViterbiDeviceParameters {
	unsigned int KmerLength;
	unsigned int SignalLevels;
	unsigned int BatchLength;
	unsigned int BatchOverlap;
	unsigned int NumInstances;
	unsigned int DurationBits;

	float* ObservationTable;
	float* ExplicitDurationTable;
	float* TransitionTable;

	float DurationTailExponent;
};


struct ViterbiInstance {
	unsigned int SignalPosition;
	unsigned int SignalLength;
	std::vector<unsigned int> Signal;
	std::vector<int16_t> RawData;
	std::vector<unsigned int> StateOutput;
	std::string Id;
};


// Common Viterbi data per GPU device
class ViterbiDevice {
public:
	ViterbiDevice(const ViterbiDeviceParameters& DeviceParams);
	~ViterbiDevice();

	void ProcessBatch();

	// Viterbi batch operations (used internally)
	void Initialize();
	void Propagate();
	void Backtrack();
	void Finalize();

	// Data loading (to be supplemented with a feeder of some type)
	void LoadData(unsigned int n, Fast5Reader &Reader);
	void WriteData(unsigned int n);
	void WriteDataFull(std::string fname, unsigned int n);

	// Code to test if the instance is idle
	unsigned int NumInstances() const;
	bool InstanceIdle(unsigned int instance) const;
	bool AllIdle() const;
	bool InstanceFinished(unsigned int instance) const;

public:
	// User defined constants
	unsigned int kNumInstances = 2;
	unsigned int kKmerLength = 5;
	unsigned int kSignalLevels = 101;
	unsigned int kBatchLength = 1024;
	unsigned int kBatchOverlap = 128;
	unsigned int kThreadsPerBlock = 512;
	unsigned int kDurationBits = 4;

	// Derrived constants
	unsigned int kTotalKmer;
	unsigned int kTotalStates;
	unsigned int kMaxDuration;

	unsigned int TotalBasesDecoded = 0;

private:
	// Pointers to lookup table structures
	float* ObservationTable = NULL;
	float* DurationTable = NULL;
	float* TransitionTable = NULL;

	// Pointers to woring memory buffers on the device
	float* CostMatrix = NULL;
	unsigned int* TracebackMatrix = NULL;
	unsigned int* StateOutputBuffer = NULL;

	// Index of corresponding CUDA device (maybe not needed)
	unsigned int cudaDeviceNr;

	// Decoding state counters
	unsigned int BatchPosition = 0;
	unsigned int CurrentBuffer = 0;

	// Array of arrays holding the input and output data for each instance
	std::vector<ViterbiInstance> Instance;
};

// Cuda device interface
int GetDeviceCount();
void SetActiveDevice(int device);