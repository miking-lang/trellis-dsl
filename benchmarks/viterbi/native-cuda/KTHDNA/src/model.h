#pragma once

#include<string>

class ViterbiModel {
public:
	ViterbiModel(const std::string &model);
	~ViterbiModel();

	// Enable saving of model
	void SaveModel(const std::string& model);

	// Make model logarithmic for Viterbi
	void Logarithmic();

	// Parameters of the model
	unsigned int KmerLength;
	//unsigned int KmerCenter;
	unsigned int DurationLength;
	unsigned int DurationBits;

	// Pointers to probability lookup tables
	float* ObservationTable;
	float* ExplicitDurationTable;
	float* TransitionTable;

	// Geometrically distributed tail of 
	float TailFactor;
	float DurationTailExponent;

	unsigned int SignalLevels;

	// Signal Normalization parameters
	float LowClip;
	float HighClip;
};