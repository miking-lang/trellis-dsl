#pragma once

#include <vector>
#include <cstdint>

class Histogram {
public:

	Histogram();
	~Histogram();

	void Add(int pos);
	void Sub(int pos);

	int Median();
	void Reset();

private:

	int* histogram; // Stor histogram
	int num_samples;
	int mid_point;
	int mid_sum;

};

class Signal {

public:
	static void Normalize(std::vector<unsigned int>& signal, std::vector<int16_t> raw, int WindowSize, unsigned int SignalLevels, float LowClip, float HighClip);
	static int NormalizationMethod;

};
