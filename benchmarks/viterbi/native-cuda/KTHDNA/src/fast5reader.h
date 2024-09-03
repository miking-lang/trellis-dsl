#pragma once

#include<queue>
#include<vector>
#include<string>

#include "H5Cpp.h"
#include "model.h"

class Fast5Reader {
public:
	Fast5Reader(const std::vector<std::string> &inputs, const ViterbiModel &model);
	~Fast5Reader();

	// Obtain the next signal to process
	void ReadSignal(std::vector<unsigned int> &signal, std::vector<int16_t>& RawData, std::string &id_str);

private:
	// Queue of files to base call
	std::queue<std::string> file_queue_;

	// Keep track of file and current read in multiread file
	H5::H5File *h5_file_;
	double file_version_;
    bool multi_read_;
	int read_number_;
	hsize_t num_reads_;

	// Used for normalizing fast5 inputs
	float low_clip_;
	float high_clip_;
	unsigned int signal_levels_;
};
