
#include "cuda_runtime.h"
#include "device_launch_parameters.h"
#include "cuda.h"

#include "baumwelch.h"
#include "model.h"

#include "stdio.h"

//#include "device_params.h"

// New C++ inlcudes
#include <iostream>
#include <vector>
#include <string>
#include <cmath>
#include <chrono>
using namespace std;
using namespace std::chrono;

// Global constants for max cuda device resources
//constexpr unsigned int kMaxNumInstances = 512;
constexpr unsigned int kDurationTableMaxLength = 64;
//constexpr unsigned int kThreadsPerBlock = 64;

// Parameters that are now fixed, but some of which should be made adjustable
constexpr int BufferLength = 1024;
//constexpr int DurationLength = 16;
constexpr int WindowLength = 32; // Cannot easily be changed (based on CUDA properties)
//constexpr int WindowCenter = 16;
constexpr int NumInstances = 512;

// Forward backward working buffers (allocated on GPU)
float* AlphaBuffer;
float* GammaBufferR;
float* BranchBufferT;
float* BranchBufferC;
float* FitBuffer;

// Buffers needed for Viterbi mapping
uint32_t* RetraceBuffer;
float* ViterbiCostBuffer;

// Accumulation buffers for learning
float* BranchBufferR;
float* ObservationTable;


/*

	CUDA Kernel functions

*/

// Ad hoc constants for first implementation (these depend on the GPU only and can remain)
constexpr unsigned int kDurationShift = 5;
//constexpr unsigned int kDurationMask = DurationLength - 1;
//constexpr unsigned int kKmerShift = 0;
constexpr unsigned int kKmerMask = WindowLength - 1;
//constexpr unsigned int kInstanceShift = 5+4;
//constexpr unsigned int kInstanceShiftShort = 4; // Does this assume that DurationLength = 16??

namespace gpuDev
{

	__constant__ float durationCostTable[kDurationTableMaxLength];
	__constant__ float TailFactor;

	__constant__ unsigned int DurationLength;
	__constant__ unsigned int SignalLevels;
	__constant__ unsigned int KmerSize;

	// Buffers on the GPU
	float* ObservationBuffer;
	unsigned int* KmerBuffer;
	unsigned int* SignalBuffer;
	int* ShiftBuffer;

	// Assumes that the window length is 32
	__device__
	void warpReduce(volatile float* sdata, int tid) {
		sdata[tid] += sdata[tid + 16];
		sdata[tid] += sdata[tid + 8];
		sdata[tid] += sdata[tid + 4];
		sdata[tid] += sdata[tid + 2];
		sdata[tid] += sdata[tid + 1];
	}

	// Size of block at most 32 to have all threads in same warp. Process the entire buffer.
	__global__
	void ForwardComputation(float* AlphaBuffer, const float* __restrict__ ObservationBuffer, const int* ShiftBuffer, float* FitBuffer) {
		extern __shared__ float sdata[];
		
		// Shift buffer to correct position
		AlphaBuffer += WindowLength * DurationLength * blockIdx.x;
		ObservationBuffer += WindowLength * blockIdx.x;
		ShiftBuffer += blockIdx.x;

		// Setup buffer pointers
		const unsigned int currentKmer = threadIdx.x;
		float* currentCost = AlphaBuffer;
		float* previousCost;

		// Initialize fist step of Alpha Buffer
		{
			float obs = ObservationBuffer[currentKmer];
			for (int d = 0; d < DurationLength; d++) {
				currentCost[currentKmer + (d << kDurationShift)] = obs;
			}
			// Normalization constant
			float norm;

			// Normalize data from initialization (maybe not nessessary after all)
			sdata[currentKmer] = obs * DurationLength;
			warpReduce(sdata, currentKmer);
			if (currentKmer == 0) FitBuffer[blockIdx.x] += log(sdata[0]); // First sample is not representative
			if (sdata[0] < 1e-16) {
				norm = 0;
			}
			else {
				norm = 1 / sdata[0];
			}
			for (int d = 0; d < DurationLength; d++) {
				currentCost[currentKmer + (d << kDurationShift)] *= norm; // Normalize data
			}

			// Step foward in buffer
			previousCost = currentCost;
			currentCost += WindowLength * DurationLength * NumInstances;
			ObservationBuffer += WindowLength * NumInstances;
		}

		// Propagate alpha buffer values
		for (int m = 1; m < BufferLength; m++) {
			float obs = ObservationBuffer[currentKmer];
			int shift = ShiftBuffer[m * NumInstances];
			float asum = 0.0f; // Cumulative cost for normalization 

			// Branch from previous segment
			float alpha0 = previousCost[(currentKmer + shift - 1) & kKmerMask];

			for (int d = 0; d < DurationLength - 2; d++) {
				float alpha1 = previousCost[currentKmer + shift + ((d + 1) << kDurationShift)];
				float bcost = durationCostTable[d] * alpha0 + alpha1;
				float cost = bcost * obs;
				currentCost[currentKmer + (d << kDurationShift)] = cost;
				asum += cost;
			}
			{
				int d = DurationLength - 2;
				float alpha1 = previousCost[currentKmer + shift + ((d + 1) << kDurationShift)];
				float bcost = durationCostTable[d] * alpha0 + (1 - TailFactor) * alpha1;
				float cost = bcost * obs;
				currentCost[currentKmer + (d << kDurationShift)] = cost;
				asum += cost;
			}
			{
				int d = DurationLength - 1;
				float alpha1 = previousCost[currentKmer + shift + ((d) << kDurationShift)];
				float bcost = durationCostTable[d] * alpha0 + TailFactor * alpha1;
				float cost = bcost * obs;
				currentCost[currentKmer + (d << kDurationShift)] = cost;
				asum += cost;
			}

			// Normalization constant
			float norm;

			// Normalize alpha data (rely on internal warp synchronization)
			sdata[currentKmer] = asum;
			warpReduce(sdata, currentKmer);
			if (currentKmer == 0) FitBuffer[blockIdx.x] += log(sdata[0]);
			if (sdata[0] < 1e-16) {
				norm = 0;
			}
			else {
				norm = 1 / sdata[0];
			}
			for (int d = 0; d < DurationLength; d++) {
				currentCost[currentKmer + (d << kDurationShift)] *= norm; // Normalize data
			}

			// Step foward in buffer
			previousCost = currentCost;
			currentCost += WindowLength * DurationLength * NumInstances;
			ObservationBuffer += WindowLength * NumInstances;
		}
	}

	// Size of block at most 32 to have all threads in same warp. Process the entire buffer.
	__global__
	void BackwardComputation(float* AlphaBuffer, float* GammaBufferR, float* BranchBufferT, float* BranchBufferC, const float* __restrict__ ObservationBuffer, const int* ShiftBuffer) {
		extern __shared__ float sdata[];

		// Shift buffer to correct position
		AlphaBuffer += WindowLength * DurationLength * blockIdx.x;
		ObservationBuffer += WindowLength * blockIdx.x + (BufferLength - 1) * WindowLength * NumInstances;
		GammaBufferR += WindowLength * blockIdx.x;
		BranchBufferT += 2 * WindowLength * DurationLength * blockIdx.x;
		BranchBufferC += 2 * WindowLength * DurationLength * blockIdx.x;
		ShiftBuffer += blockIdx.x;

		// Setup buffer pointers
		const unsigned int currentKmer = threadIdx.x;
		float* currentCost = AlphaBuffer + (BufferLength - 1) * WindowLength * DurationLength * NumInstances;
		float* gammaPointerR = GammaBufferR + (BufferLength - 1) * WindowLength * NumInstances;
		float* previousCost;

		// Initialize fist step of Beta Buffer
		{
			float gsum = 0.0f;
			for (int d = 0; d < DurationLength; d++) { // Gamma = Alpha in last time slot (clean this up later) 
				gsum += currentCost[currentKmer + (d << kDurationShift)];
			}
			gammaPointerR[currentKmer] = gsum;
			for (int d = 0; d < DurationLength; d++) {
				currentCost[currentKmer + (d << kDurationShift)] = 1.0f;
			}
			// Normalize data from initialization (maybe not nessessary after all)
			sdata[currentKmer] = DurationLength;
			warpReduce(sdata, currentKmer);
			for(unsigned int d = 0; d < DurationLength; d++) {
				currentCost[currentKmer + (d << kDurationShift)] /= sdata[0]; // Normalize data
			}

			// Step backward in buffer
			previousCost = currentCost - WindowLength * DurationLength * NumInstances;
			gammaPointerR -= WindowLength * NumInstances;
		}
		// Propagate beta buffer values
		for (int m = BufferLength - 1; m > 0; m--) {
			float obs = ObservationBuffer[currentKmer];
			int shift = ShiftBuffer[m * NumInstances];
			float bsum = 0.0f; // Cumulative cost for normalization of beta
			float gsum = 0.0f; // Cumulative cost for normalization of gamma
			float brsum = 0.0f; // Cumulative cost for normalization of branches
			float alpha0 = previousCost[(currentKmer + shift - 1) & kKmerMask];
			float branch;

			float cost0 = 0.0f;
			for (int d = 0; d < DurationLength - 2; d++) {
				float beta = currentCost[currentKmer + (d << kDurationShift)];

				// Branch into end state
				branch = durationCostTable[d] * beta * obs;
				brsum += BranchBufferT[currentKmer + (d << kDurationShift)] = alpha0 * branch;
				cost0 += branch;

				// Branch into continuation state
				float cost = beta * obs;
				float alpha = previousCost[currentKmer + shift + ((d + 1) << kDurationShift)];
				bsum += previousCost[currentKmer + shift + ((d + 1) << kDurationShift)] = cost;
				cost *= alpha;
				gsum += cost;
				brsum += BranchBufferT[currentKmer + ((d+DurationLength) << kDurationShift)] = cost;
			}
			{
				// Second to last duration state
				float betaA = currentCost[currentKmer + ((DurationLength - 2) << kDurationShift)];
				branch = durationCostTable[DurationLength - 2] * betaA * obs;
				brsum += BranchBufferT[currentKmer + ((DurationLength - 2) << kDurationShift)] = alpha0 * branch;
				cost0 += branch;

				// Last duration state
				float betaB = currentCost[currentKmer + ((DurationLength - 1) << kDurationShift)];
				branch = durationCostTable[DurationLength - 1] * betaB * obs;
				brsum += BranchBufferT[currentKmer + ((DurationLength - 1) << kDurationShift)] = alpha0 * branch;
				cost0 += branch;

				// Branch into last state
				float alpha = previousCost[currentKmer + shift + ((DurationLength - 1) << kDurationShift)];
				
				float branchA = (1 - TailFactor) * betaA * obs;
				brsum += BranchBufferT[currentKmer + ((2*DurationLength-2) << kDurationShift)] = alpha * branchA;

				float branchB = TailFactor * betaB* obs;
				brsum += BranchBufferT[currentKmer + ((2*DurationLength-1) << kDurationShift)] = alpha * branchB;
				
				float cost = branchA + branchB;
				bsum += previousCost[currentKmer + shift + ((DurationLength - 1) << kDurationShift)] = cost;
				cost *= alpha;
				gsum += cost;
			}
			{ // Branch out of last segment
				float cost = cost0;
				bsum += previousCost[(currentKmer + shift - 1) & kKmerMask] = cost;
				cost *= alpha0;
				gsum += cost;
			}

			// Normalization constant
			float norm;

			// Normalize beta data (rely on internal warp synchronization)
			sdata[currentKmer] = bsum;
			warpReduce(sdata, currentKmer);
			if (sdata[0] < 1e-16) {
				norm = 0;
			}
			else {
				norm = 1 / sdata[0];
			}
			for (int d = 0; d < DurationLength; d++) {
				previousCost[currentKmer + (d << kDurationShift)] *= norm; // Normalize data
			}
			// Normalize gamma data (rely on internal warp synchronization)
			sdata[currentKmer] = gsum;
			warpReduce(sdata, currentKmer);
			//if ((sdata[0] < 1e-14) && (threadIdx.x == 0)) {
			//if ((sdata[0] < 1e-20) && (threadIdx.x == 0)) {
			//	printf("*** Bad gamma buffer at position : %d\n", m);
			//}
			if (sdata[0] < 1e-16) {
				norm = 0;
			}
			else {
				norm = 1 / sdata[0];
			}
			gammaPointerR[currentKmer] = gsum * norm; // Use gsum directly to summarize state probabilities
			// Normalize branch data (rely on internal warp synchronization)
			sdata[currentKmer] = brsum;
			warpReduce(sdata, currentKmer);
			if (sdata[0] < 1e-16) {
				norm = 0;
			}
			else {
				norm = 1 / sdata[0];
			}
			for (int d = 0; d < 2*DurationLength; d++) {
				BranchBufferC[currentKmer + (d << kDurationShift)] += BranchBufferT[currentKmer + (d << kDurationShift)] * norm; // Cumulate saved data
			}

			// Step backward in buffer
			currentCost = previousCost; // NO REAL NEED TO SAVE ENTIRE BETA BUFFER IN MEMORY
			previousCost -= WindowLength * DurationLength * NumInstances;
			ObservationBuffer -= WindowLength * NumInstances;
			gammaPointerR -= WindowLength * NumInstances;
		}
	}

	// Add code for reduction of probabilities...
	/*
	__global__
	StateReduction(const float* __restrict__ GammaBuffer, )
	*/

	// Reduce the branch probabilies over winodow positins and instances
	__global__
	void BranchReduction(float* BranchBufferR, const float* BranchBufferC) {
		extern __shared__ float sdata[];
		
		unsigned int tid = threadIdx.x;
		unsigned int bid = blockIdx.x;
		unsigned int branch = bid & (2 * DurationLength - 1);
		unsigned int instance = bid / (2 * DurationLength);

		//printf("Instance : %d, Branch %d\n", instance, branch);

		// Shift to correct instance
		BranchBufferC += instance * 2 * WindowLength * DurationLength;

		// Load one element to shared memory
		sdata[tid] = BranchBufferC[tid + (branch << kDurationShift)];
		
		// Reduce over warp
		warpReduce(sdata, tid);

		// Store reduced value
		if(tid == 0) atomicAdd(&BranchBufferR[branch], sdata[0]);
	}

	__global__
	void BuildObservations(const unsigned int* KmerBuffer, const unsigned int* SignalBuffer, const float* GammaBufferR, float* ObservationTable) {
		unsigned int thread = blockIdx.x * blockDim.x + threadIdx.x;
		unsigned int instance = (thread / WindowLength) & (NumInstances - 1);

		unsigned int sigpos = thread / WindowLength;
		unsigned int kmer = KmerBuffer[thread];
		unsigned int siglev = SignalBuffer[sigpos];

		// Add state probabiility to the right place
		atomicAdd(&ObservationTable[kmer + (siglev << (2 * KmerSize))], GammaBufferR[thread]);
	}

	// Size of block at most 32 to have all threads in same warp. Process the entire buffer using Viterbi decoding.
	__global__
		void ViterbiComputation(uint32_t* RetraceBuffer, float* ViterbiCostBuffer, float* GammaBufferR, const float* __restrict__ ObservationBuffer, const int* ShiftBuffer) {
		extern __shared__ float sdata[];

		// Shift buffer to correct position
		RetraceBuffer += WindowLength * DurationLength * blockIdx.x;
		ViterbiCostBuffer += WindowLength * DurationLength * blockIdx.x;
		GammaBufferR += WindowLength * blockIdx.x;
		ObservationBuffer += WindowLength * blockIdx.x;
		ShiftBuffer += blockIdx.x;

		// Setup buffer pointers
		const unsigned int currentKmer = threadIdx.x;
		float* currentCost = ViterbiCostBuffer;
		float* previousCost = ViterbiCostBuffer + WindowLength * DurationLength * NumInstances;
		float* tmpCost;

		// Initialize fist step of ViterbiCostBuffer
		{
			float obs = ObservationBuffer[currentKmer];
			for (int d = 0; d < DurationLength; d++) {
				currentCost[currentKmer + (d << kDurationShift)] = obs;
			}
			// Normalization constant
			float norm;

			// Normalize data from initialization (maybe not nessessary after all)
			sdata[currentKmer] = obs * DurationLength;
			warpReduce(sdata, currentKmer);
			if (sdata[0] < 1e-16) {
				norm = 0;
			}
			else {
				norm = 1 / sdata[0];
			}
			for (int d = 0; d < DurationLength; d++) {
				currentCost[currentKmer + (d << kDurationShift)] *= norm; // Normalize data
			}

			// Step foward in buffer
			tmpCost = previousCost; // Just swap buffer pointers
			previousCost = currentCost;
			currentCost = tmpCost;
			ObservationBuffer += WindowLength * NumInstances;
			RetraceBuffer += WindowLength * DurationLength * NumInstances;
		}

		// Propagate maximum buffer cost values
		for (int m = 1; m < BufferLength; m++) {
			float obs = ObservationBuffer[currentKmer];
			int shift = ShiftBuffer[m * NumInstances];
			float asum = 0.0f; // Cumulative cost for normalization 

			// Branch from previous segment
			float alpha0 = previousCost[(currentKmer + shift - 1) & kKmerMask];

			for (int d = 0; d < DurationLength - 2; d++) {
				float alpha1 = previousCost[(currentKmer + shift) + ((d + 1) << kDurationShift)];
				float new_seg_cost = durationCostTable[d] * alpha0;
				float old_seg_cost = alpha1;
				float bcost;
				if (new_seg_cost > old_seg_cost) { // Better to start a new segment
					bcost = new_seg_cost;
					RetraceBuffer[currentKmer + (d << kDurationShift)] = (currentKmer + shift - 1) & kKmerMask;
				}
				else {
					bcost = old_seg_cost;
					RetraceBuffer[currentKmer + (d << kDurationShift)] = (currentKmer + shift) + ((d + 1) << kDurationShift);
				}
				float cost = bcost * obs;
				currentCost[currentKmer + (d << kDurationShift)] = cost;
				asum += cost;
			}
			{
				int d = DurationLength - 2;
				float alpha1 = 0; // previousCost[(currentKmer + shift) + ((d + 1) << kDurationShift)];
				float new_seg_cost = durationCostTable[d] * alpha0;
				float old_seg_cost = (1 - TailFactor) * alpha1;;
				float bcost;
				if (new_seg_cost > old_seg_cost) { // Better to start a new segment
					bcost = new_seg_cost;
					RetraceBuffer[currentKmer + (d << kDurationShift)] = (currentKmer + shift - 1) & kKmerMask;
				}
				else {
					bcost = old_seg_cost;
					RetraceBuffer[currentKmer + (d << kDurationShift)] = (currentKmer + shift) + ((d + 1) << kDurationShift);
				}
				float cost = bcost * obs;
				currentCost[currentKmer + (d << kDurationShift)] = cost;
				asum += cost;
			}
			{
				int d = DurationLength - 1;
				float alpha1 = previousCost[currentKmer + shift + ((d) << kDurationShift)];
				float new_seg_cost = durationCostTable[d] * alpha0;
				float old_seg_cost = TailFactor * alpha1;
				float bcost;
				if (new_seg_cost > old_seg_cost) { // Better to start a new segment
					bcost = new_seg_cost;
					RetraceBuffer[currentKmer + (d << kDurationShift)] = (currentKmer + shift - 1) & kKmerMask;
				}
				else {
					bcost = old_seg_cost;
					RetraceBuffer[currentKmer + (d << kDurationShift)] = (currentKmer) + shift + ((d) << kDurationShift);
				}
				float cost = bcost * obs;
				currentCost[currentKmer + (d << kDurationShift)] = cost;
				asum += cost;
			}

			// Normalization constant
			float norm;

			// Normalize alpha data (rely on internal warp synchronization)
			sdata[currentKmer] = asum;
			warpReduce(sdata, currentKmer);
			if (sdata[0] < 1e-16) {
				norm = 0;
			}
			else {
				norm = 1 / sdata[0];
			}
			for (int d = 0; d < DurationLength; d++) {
				currentCost[currentKmer + (d << kDurationShift)] *= norm; // Normalize data
			}

			// Step foward in buffer
			tmpCost = previousCost; // Just swap buffer pointers
			previousCost = currentCost;
			currentCost = tmpCost;
			ObservationBuffer += WindowLength * NumInstances;
			RetraceBuffer += WindowLength * DurationLength * NumInstances;
		}

		// Backtrack using single thread
		if (currentKmer == 0) {
			// Search for the maximum final state
			currentCost = previousCost;
			int state = 0;
			float max_cost = 0;
			for (int s = 0; s < WindowLength * DurationLength; s++) {
				if (currentCost[s] > max_cost) {
					state = s;
					max_cost = currentCost[s];
				}
			}
			//printf("Max state : %d\n", state);

			// Retrace the steps of the algorithm... (and maby fill in GammaR buffer first to verify the computation seems correct)
			RetraceBuffer -= WindowLength * DurationLength * NumInstances; // Rewind
			float* gammaPointerR = GammaBufferR + (BufferLength - 1) * WindowLength * NumInstances;
			for(int m = (BufferLength - 1); m >= 0; m--) {
				gammaPointerR[state & kKmerMask] = 1.0;
				gammaPointerR -= WindowLength * NumInstances;
				state = RetraceBuffer[state];
				RetraceBuffer -= WindowLength * DurationLength * NumInstances; // Rewind
			}
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

extern float *BranchBufferRDebug;
extern float *ObservationTableDebug;
extern float* FitBufferDebug;
extern float* GammaBufferDebug;

void
GPUSetup(ViterbiModel& Model) {
	cudaError_t status;

	float* DurationTable = Model.ExplicitDurationTable;
	float TailFactor = Model.TailFactor;
	unsigned int SignalLevels = Model.SignalLevels;
	unsigned int KmerSize = Model.KmerLength;
	unsigned int DurationLength = Model.DurationLength;

	// Check to see that we do not go overboard with duratuon length
	if (DurationLength > kDurationTableMaxLength) {
		cerr << "ERROR: Current version only support explicit durations up to lenght 64" << endl;
		exit(0);
	}

	// Allocate memory for CUDA input buffers
	status = cudaMalloc(&gpuDev::ObservationBuffer, (WindowLength * NumInstances * BufferLength) * sizeof(float));
	if (status != cudaSuccess) throw CUDAException();
	status = cudaMalloc(&gpuDev::KmerBuffer, (WindowLength * NumInstances * BufferLength) * sizeof(float));
	if (status != cudaSuccess) throw CUDAException();
	status = cudaMalloc(&gpuDev::SignalBuffer, NumInstances * BufferLength * sizeof(int));
	if (status != cudaSuccess) throw CUDAException();
	status = cudaMalloc(&gpuDev::ShiftBuffer, NumInstances * BufferLength * sizeof(int));
	if (status != cudaSuccess) throw CUDAException();

	// Allocate memory for CUDA working buffers
	status = cudaMalloc(&AlphaBuffer, (WindowLength * DurationLength * NumInstances * BufferLength) * sizeof(float));
	if (status != cudaSuccess) throw CUDAException();
	// Repurpose Alpha buffer for Viterbi retracing
	RetraceBuffer = (uint32_t*)AlphaBuffer;

	status = cudaMalloc(&GammaBufferR, (WindowLength * NumInstances * BufferLength) * sizeof(float));
	if (status != cudaSuccess) throw CUDAException();
	status = cudaMalloc(&BranchBufferT, (2 * WindowLength * DurationLength * NumInstances) * sizeof(float));
	if (status != cudaSuccess) throw CUDAException();

	status = cudaMalloc(&BranchBufferR, (2 * DurationLength * NumInstances) * sizeof(float));
	if (status != cudaSuccess) throw CUDAException();
	status = cudaMalloc(&ObservationTable, ((1 << (2 * KmerSize)) * SignalLevels) * sizeof(float));
	if (status != cudaSuccess) throw CUDAException();

	status = cudaMalloc(&BranchBufferC, (2 * WindowLength * DurationLength * NumInstances) * sizeof(float));
	if (status != cudaSuccess) throw CUDAException();

	status = cudaMalloc(&FitBuffer, NumInstances * sizeof(float));
	if (status != cudaSuccess) throw CUDAException();

	// Allocate running ocst buffers for Viterbi algorithm
	status = cudaMalloc(&ViterbiCostBuffer, (WindowLength * DurationLength * NumInstances * 2 + 1) * sizeof(float)); // + 1 needed so that previous cost can read outside of buffer
	if (status != cudaSuccess) throw CUDAException();

	// Reset long runing buffers used for data collection
	status = cudaMemset(BranchBufferR, 0, (2 * DurationLength * NumInstances) * sizeof(float)); // Could also be done in code?
	if (status != cudaSuccess) throw CUDAException();
	status = cudaMemset(ObservationTable, 0, ((1 << (2 * KmerSize)) * SignalLevels) * sizeof(float)); // Could also be done in code?
	if (status != cudaSuccess) throw CUDAException();
	status = cudaMemset(FitBuffer, 0, NumInstances * sizeof(float)); // Could also be done in code?
	if (status != cudaSuccess) throw CUDAException();

	// Fill constants for duration table and tail exponent
	status = cudaMemcpyToSymbol(gpuDev::durationCostTable, DurationTable, DurationLength * sizeof(float), 0, cudaMemcpyHostToDevice);
	if (status != cudaSuccess) throw CUDAException();
	status = cudaMemcpyToSymbol(gpuDev::DurationLength, &DurationLength, sizeof(unsigned int), 0, cudaMemcpyHostToDevice);
	if (status != cudaSuccess) throw CUDAException();
	status = cudaMemcpyToSymbol(gpuDev::TailFactor, &TailFactor, sizeof(float), 0, cudaMemcpyHostToDevice);
	if (status != cudaSuccess) throw CUDAException();
	status = cudaMemcpyToSymbol(gpuDev::SignalLevels, &SignalLevels, sizeof(unsigned int), 0, cudaMemcpyHostToDevice);
	if (status != cudaSuccess) throw CUDAException();
	status = cudaMemcpyToSymbol(gpuDev::KmerSize, &KmerSize, sizeof(unsigned int), 0, cudaMemcpyHostToDevice);
	if (status != cudaSuccess) throw CUDAException();

}

// Deallocate memory on GPU
void
GPUCleanup() {
	cudaFree(AlphaBuffer);
	cudaFree(GammaBufferR);
	cudaFree(BranchBufferT);
	cudaFree(BranchBufferC);
	cudaFree(BranchBufferR);
	cudaFree(FitBuffer);
	cudaFree(ViterbiCostBuffer);
	cudaFree(ObservationTable);
	cudaFree(gpuDev::ObservationBuffer);
	cudaFree(gpuDev::KmerBuffer);
	cudaFree(gpuDev::SignalBuffer);
	cudaFree(gpuDev::ShiftBuffer);
}

void
GPUAlphaBetaCompute(ViterbiModel& Model, float* ObservationBuffer, unsigned int*KmerBuffer, unsigned int* SignalBuffer, int* ShiftBuffer) {
	cudaError_t status;

	// Quick fix. Make more elegant later
	unsigned int DurationLength = Model.DurationLength;

	//high_resolution_clock::time_point t1, t2;

	// Reset this buffer before each batch of instances
	status = cudaMemset(BranchBufferC, 0, (2 * WindowLength * DurationLength * NumInstances) * sizeof(float)); // Could also be done in code?
	if (status != cudaSuccess) throw CUDAException();

	// Copy memory to CUDA buffers
	//t1 = high_resolution_clock::now();
	status = cudaMemcpy(gpuDev::ObservationBuffer, ObservationBuffer, sizeof(float) * (WindowLength * NumInstances * BufferLength), cudaMemcpyHostToDevice);
	if (status != cudaSuccess) throw CUDAException();
	status = cudaMemcpy(gpuDev::KmerBuffer, KmerBuffer, sizeof(float) * (WindowLength * NumInstances * BufferLength), cudaMemcpyHostToDevice);
	if (status != cudaSuccess) throw CUDAException();
	status = cudaMemcpy(gpuDev::SignalBuffer, SignalBuffer, sizeof(int) * (NumInstances * BufferLength), cudaMemcpyHostToDevice);
	if (status != cudaSuccess) throw CUDAException();
	status = cudaMemcpy(gpuDev::ShiftBuffer, ShiftBuffer, sizeof(int) * (NumInstances * BufferLength), cudaMemcpyHostToDevice);
	if (status != cudaSuccess) throw CUDAException();	
	//t2 = high_resolution_clock::now();
	//time_span = duration_cast<duration<double>>(t2 - t1);
	//cout << "Observation copy time : " << time_span.count() << " s" << endl;
	if (status != cudaSuccess) throw CUDAException();

	// Null out FitBuffer (This will be needed to get histogram data for model to data fit over buffers)
	status = cudaMemset(FitBuffer, 0, NumInstances * sizeof(float)); // Could also be done in code?
	if (status != cudaSuccess) throw CUDAException();

	// Run GPU aided code

	// New Forward Pass (in single kernel call)
	//t1 = high_resolution_clock::now();
	gpuDev::ForwardComputation <<< NumInstances, WindowLength, 64*4 >>> (AlphaBuffer, gpuDev::ObservationBuffer, gpuDev::ShiftBuffer, FitBuffer);
	//cudaDeviceSynchronize();
	//t2 = high_resolution_clock::now();
	//time_span = duration_cast<duration<double>>(t2 - t1);
	//cout << "Forward computation time : " << time_span.count() << " s" << endl;

	// Backward pass (in single kernel call)
	//t1 = high_resolution_clock::now();
	gpuDev::BackwardComputation <<< NumInstances, WindowLength, 64 * 4 >>> (AlphaBuffer, GammaBufferR, BranchBufferT, BranchBufferC, gpuDev::ObservationBuffer, gpuDev::ShiftBuffer);
	//cudaDeviceSynchronize();
	//t2 = high_resolution_clock::now();
	//time_span = duration_cast<duration<double>>(t2 - t1);
	//cout << "Backward computation time : " << time_span.count() << " s" << endl;

	// Reduce Branch Buffer (over many parts)
	//t1 = high_resolution_clock::now();
	gpuDev::BranchReduction <<< 2 * DurationLength * NumInstances, WindowLength, 64 * 4 >>> (BranchBufferR, BranchBufferC);
	//cudaDeviceSynchronize();
	//t2 = high_resolution_clock::now();
	//time_span = duration_cast<duration<double>>(t2 - t1);
	//cout << "Branch reduction time : " << time_span.count() << " s" << endl;

	status = cudaMemcpy(BranchBufferRDebug, BranchBufferR, sizeof(float) * (2 * DurationLength), cudaMemcpyDeviceToHost);
	if (status != cudaSuccess) throw CUDAException();


	// Add to observation table
	//t1 = high_resolution_clock::now();
	gpuDev::BuildObservations <<< WindowLength * NumInstances * BufferLength / 128, 128 >>> (gpuDev::KmerBuffer, gpuDev::SignalBuffer, GammaBufferR, ObservationTable);
	//cudaDeviceSynchronize();
	//t2 = high_resolution_clock::now();
	//time_span = duration_cast<duration<double>>(t2 - t1);
	//cout << "Observation counting time : " << time_span.count() << " s" << endl;

	//status = cudaMemcpy(GammaBufferDebug, GammaBufferR, sizeof(float) * (WindowLength * BufferLength * NumInstances), cudaMemcpyDeviceToHost);
	//if (status != cudaSuccess) throw CUDAException();

	unsigned int KmerSize = Model.KmerLength;
	unsigned int SignalLevels = Model.SignalLevels;
	status = cudaMemcpy(ObservationTableDebug, ObservationTable, sizeof(float) * ((1 << (2 * KmerSize)) * SignalLevels), cudaMemcpyDeviceToHost);
	if (status != cudaSuccess) throw CUDAException();

	// Always copy this one back for histogram debugging (FIND MORE ELEGANT SOLUTION)
	status = cudaMemcpy(FitBufferDebug, FitBuffer, sizeof(float) * NumInstances, cudaMemcpyDeviceToHost);
	if (status != cudaSuccess) throw CUDAException();

	for (int i = 0; i < ((1 << (2 * KmerSize)) * SignalLevels); i++) {
		if (isnan(ObservationTableDebug[i])) {
			printf("********* NAN *********");
			exit(-1);
		}
	}

}

void
GPUViterbiCompute(ViterbiModel& Model, float* ObservationBuffer, unsigned int* KmerBuffer, unsigned int* SignalBuffer, int* ShiftBuffer) {

	cudaError_t status;

	// Quick fix. Make more elegant later
	unsigned int DurationLength = Model.DurationLength;

	// Copy memory to CUDA buffers (still needed for Viterbi training)
	status = cudaMemcpy(gpuDev::ObservationBuffer, ObservationBuffer, sizeof(float) * (WindowLength * NumInstances * BufferLength), cudaMemcpyHostToDevice);
	if (status != cudaSuccess) throw CUDAException();
	status = cudaMemcpy(gpuDev::KmerBuffer, KmerBuffer, sizeof(float) * (WindowLength * NumInstances * BufferLength), cudaMemcpyHostToDevice);
	if (status != cudaSuccess) throw CUDAException();
	status = cudaMemcpy(gpuDev::SignalBuffer, SignalBuffer, sizeof(int) * (NumInstances * BufferLength), cudaMemcpyHostToDevice);
	if (status != cudaSuccess) throw CUDAException();
	status = cudaMemcpy(gpuDev::ShiftBuffer, ShiftBuffer, sizeof(int) * (NumInstances * BufferLength), cudaMemcpyHostToDevice);
	if (status != cudaSuccess) throw CUDAException();

	// Null GammaR buffer for clear output
	status = cudaMemset(GammaBufferR, 0, (WindowLength * BufferLength * NumInstances) * sizeof(float)); // Could also be done in code?
	if (status != cudaSuccess) throw CUDAException();

	// Do the whole Viterbi computation in one sweep
	gpuDev::ViterbiComputation <<< NumInstances, WindowLength, 64 * 4 >> > (RetraceBuffer, ViterbiCostBuffer, GammaBufferR, gpuDev::ObservationBuffer, gpuDev::ShiftBuffer);

	status = cudaMemcpy(GammaBufferDebug, GammaBufferR, sizeof(float) * (WindowLength * BufferLength * NumInstances), cudaMemcpyDeviceToHost);
	if (status != cudaSuccess) throw CUDAException();

	// Build frequency count observation table
	gpuDev::BuildObservations << < WindowLength * NumInstances * BufferLength / 128, 128 >> > (gpuDev::KmerBuffer, gpuDev::SignalBuffer, GammaBufferR, ObservationTable);

	unsigned int KmerSize = Model.KmerLength;
	unsigned int SignalLevels = Model.SignalLevels;
	status = cudaMemcpy(ObservationTableDebug, ObservationTable, sizeof(float) * ((1 << (2 * KmerSize)) * SignalLevels), cudaMemcpyDeviceToHost);
	if (status != cudaSuccess) throw CUDAException();

	for (int i = 0; i < ((1 << (2 * KmerSize)) * SignalLevels); i++) {
		if (isnan(ObservationTableDebug[i])) {
			printf("********* NAN *********");
			exit(-1);
		}
	}

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