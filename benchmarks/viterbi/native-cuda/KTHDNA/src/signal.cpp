
#include "signal.h"
#include "math.h"

#include <vector>
using namespace std;

Histogram::Histogram() {
	histogram = new int[1 << 16];
	Reset();
}


Histogram::~Histogram() {
	delete[] histogram;
}

void
Histogram::Reset() {
	for (int n = 0; n < (1 << 16); n++) {
		histogram[n] = 0; // Initialize variables
	}
	num_samples = 0;
	mid_point = 0;
	mid_sum = 0;
}

void
Histogram::Add(int pos) {
	if (pos < 0) pos = 0; // Seafety code for broken reads (chech how often this happens later)
	if (num_samples == 0) mid_point = pos;
	histogram[pos]++;
	num_samples++;
	if (pos <= mid_point) {
		mid_sum++;
	}
}

void
Histogram::Sub(int pos) {
	if (pos < 0) pos = 0; // Seafety code for broken reads (check how often this happens later)
	histogram[pos]--;
	num_samples--;
	if (pos <= mid_point) {
		mid_sum--;
	}
}

int
Histogram::Median() {

	while ((mid_sum << 1) >= num_samples) {
		mid_sum -= histogram[mid_point];
		mid_point--;
	}
	if (mid_point < 0) { // Just for safety (should never happen)
		mid_point = 0;
		return 0;
	}
	int low_sum = mid_sum;
	int low_point = mid_point;
	while ((mid_sum << 1) < num_samples) {
		mid_point++;
		mid_sum += histogram[mid_point];
	}
	if (((mid_sum << 1) - num_samples) < (num_samples - (low_sum << 1))) {
		return mid_point;
	}
	else {
		return low_point;
	}
}
 
int Signal::NormalizationMethod = 0; // Static initialization

void
Signal::Normalize(std::vector<unsigned int>& signal, const std::vector<int16_t> raw, int WindowSize, unsigned int SignalLevels, float LowClip, float HighClip) {
	if (NormalizationMethod == 0) { // No normalization of the data

		// Resize signal
		int size = raw.size();
		signal.resize(size);

		// Move signal from raw to signal buffer
		for (int n = 0; n < size; n++) {
			// Signal quantization
			int sval = (int) raw[n];
			if (sval < 0) sval = 0; // Clip small signal
			if (sval >= SignalLevels) sval = SignalLevels - 1; // Clip high signal
			signal[n] = (unsigned int) sval;
		}

	}
	else // Use standard normalization
	{
		/* // Sliding window MAD normalization
		int size = raw.size();
		if ((WindowSize > size) || (WindowSize <= 0)) WindowSize = size; // Limit window length to lenght of signal
		// Compute median of raw signal over window
		Histogram hist;
		vector<int16_t> median;
		median.resize(size);
	
		int RawPos = 0;
		int MedPos = 0;
		while (RawPos < WindowSize) {
			hist.Add(raw[RawPos]);
			RawPos++;
		}
		while (MedPos < (WindowSize >> 1)) { // Fill up first half statically
			median[MedPos] = hist.Median();
			MedPos++;
		}
		while (RawPos < size) { // Fill in sliding window middle part
			hist.Add(raw[RawPos]); // Add new sample
			hist.Sub(raw[RawPos - WindowSize]); // Subtract missing sampe
			median[MedPos] = hist.Median();
			MedPos++;
			RawPos++;
		}
		while (MedPos < size) { // Fill in last part statically
			median[MedPos] = hist.Median();
			MedPos++;
		}
		// Compute signal deviations
		hist.Reset();
		vector<int16_t> deviation;
		deviation.resize(size);
		RawPos = 0;
		MedPos = 0;
		while (RawPos < WindowSize) {
			hist.Add(abs(raw[RawPos] - median[RawPos]));
			RawPos++;
		}
		while (MedPos < (WindowSize >> 1)) { // Fill up first half statically
			deviation[MedPos] = hist.Median();
			MedPos++;
		}
		while (RawPos < size) { // Fill in sliding window middle part
			hist.Add(abs(raw[RawPos] - median[RawPos])); // Add new sample
			hist.Sub(abs(raw[RawPos - WindowSize] - median[RawPos - WindowSize])); // Subtract missing sampe
			deviation[MedPos] = hist.Median();
			MedPos++;
			RawPos++;
		}
		while (MedPos < size) { // Fill in last part statically
			deviation[MedPos] = hist.Median();
			MedPos++;
		}
		// Scale signal for Viterbi
		signal.resize(size); // Make room for output signal
		for (unsigned int n = 0; n < size; n++) {
			// Signal quantization
			float sval = ((float)(raw[n] - median[n])) / ((float) deviation[n]);
			if (sval < LowClip) sval = LowClip; // Clip small signal
			if (sval > HighClip) sval = HighClip; // Clip high signal
			signal[n] = (int)round((SignalLevels - 1) * (sval - LowClip) / (HighClip - LowClip));
		}
		*/
		// Full signal z-score normalization

		int size = raw.size();

		float mean = 0.0f;
		for (int n = 0; n < size; n++) {
			mean += (float)raw[n];
		}
		mean /= size; 

		float var = 0.0f;
		for (int n = 0; n < size; n++) {
			float diff = (float)raw[n] - mean;
			var += diff * diff;
		}
		var /= size;

		float norm = (float) (1.0 / sqrt((double) var));
		signal.resize(size); // Make room for output signal
		for (int n = 0; n < size; n++) {
			float sval = ((float)raw[n] - mean) * norm;
			if (sval < LowClip) sval = LowClip; // Clip small signal
			if (sval > HighClip) sval = HighClip; // Clip high signal
			signal[n] = (int)round((SignalLevels - 1) * (sval - LowClip) / (HighClip - LowClip));
		}	
	}

}
