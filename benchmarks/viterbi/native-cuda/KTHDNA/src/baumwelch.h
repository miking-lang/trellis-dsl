#pragma once

#include "model.h"

void GPUSetup(ViterbiModel& Model);
void GPUCleanup();
void GPUAlphaBetaCompute(ViterbiModel& Model, float* ObservationBuffer, unsigned int* KmerBuffer, unsigned int* SignalBuffer, int* StateShiftBuffer);
void GPUViterbiCompute(ViterbiModel& Model, float* ObservationBuffer, unsigned int* KmerBuffer, unsigned int* SignalBuffer, int* StateShiftBuffer);

// Cuda device interface
int GetDeviceCount();
void SetActiveDevice(int device);