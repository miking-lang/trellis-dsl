// Class for parsing fast5 files and obtaining raw data for each concequitive read

#include "fast5reader.h"
#include "model.h"
#include "signal.h"

#include <iostream>
#include <vector>
#include <math.h>

#include "H5Cpp.h"
using namespace H5;
using namespace std;

#include <boost/filesystem.hpp>
namespace fs = boost::filesystem;

Fast5Reader::Fast5Reader(const vector<string>& inputs, const ViterbiModel &model) 
	: h5_file_(nullptr), file_version_(0), multi_read_(true)
{

	// Set model parameters
	low_clip_ = model.LowClip;
	high_clip_ = model.HighClip;
	signal_levels_ = model.SignalLevels;

	// Initialize with files in input directory
	clog << "Building input file queue..." << endl;

	for (auto input = inputs.begin(); input < inputs.end(); input++) {
		if (fs::is_regular_file(*input)) { // Should really check fast5 extension
			file_queue_.push(*input);
			clog << *input << endl;
		}
		if (fs::is_directory(*input)) {
			for (auto& p : fs::recursive_directory_iterator(*input)) {
				if (fs::is_regular_file(p) && (p.path().extension().compare(fs::path(".fast5")) == 0)) {
					string pname = p.path().string();
					clog << pname << endl; // Print out file name
					file_queue_.push(pname);
				}
			}
		}
	}

	// Set up counters for multi read input
	read_number_ = 0;
	num_reads_ = 0;
}

Fast5Reader::~Fast5Reader() {
	if(h5_file_) delete h5_file_;
}

// Need to clean this up by dividing code

vector<int16_t> Medians;
vector<uint16_t> Deviations;

void
Fast5Reader::ReadSignal(std::vector<unsigned int> &signal, std::vector<int16_t> &RawData, std::string &id_str) {

	if (file_queue_.empty()) {
		signal.resize(0); // No more signal to process
	}
	else {
		// Get file from file queue
		string fname = file_queue_.front();
		// file_queue_.pop(); // Take care of this at the end of the file

		try {
			// Open a new file
			if (read_number_ == 0) {
				h5_file_ = new H5File(fname, H5F_ACC_RDONLY);

				// Obtain file version (to know how to read file)
				Attribute version = h5_file_->openAttribute("file_version");
				H5T_class_t type_class = version.getTypeClass();

				if (type_class == H5T_STRING) { // Version stored as a string
					H5::StrType version_type = version.getStrType();
					std::string version_str;
					hsize_t version_size = version.getStorageSize();
					version.read(version_type, version_str);
					file_version_ = std::stod(version_str);
				}
				else if (type_class == H5T_FLOAT) { // Version stored as a double (typical for older format)
					version.read(PredType::IEEE_F64LE, &file_version_);
				}
				else {
					cerr << "ERROR: unrecognized type class for version number." << endl;
					exit(1);
				}
                
                // Check if the file is a multi read file (not relying on version number)
                multi_read_ = true; // Assume so if not proven wrong, and try to open
                num_reads_ = h5_file_->getNumObjs();
                for(int i=0; i < num_reads_; i++) {
                    H5std_string objName = h5_file_->getObjnameByIdx(i);
                    if (objName.rfind("read_", 0) == 0) { // definitely a multi-read file
                        break;
                    } else if (objName.rfind("UniqueGlobalKey", 0) == 0) { // This group indicate singe read file
                        num_reads_ = 1; // Treat file as single read
                        multi_read_ = false;
                        break;
                    }
                }

			}
			
			// Get current read from file
			Group read;
			if (multi_read_) {
				H5std_string readName = h5_file_->getObjnameByIdx(read_number_);
				readName.append("/Raw");
				read = h5_file_->openGroup(readName);
			}
			else { // Single read file
				Group reads = h5_file_->openGroup("/Raw/Reads");
				H5std_string readName = reads.getObjnameByIdx(read_number_);
				read = reads.openGroup(readName);
			}

			// Obtain the read id (mainly for printing it in fasta or fastq file)
			Attribute read_id = read.openAttribute("read_id");
			H5::StrType read_type = read_id.getStrType();
			read_id.read(read_type, id_str);

			// Obtain the length of the raw read
			Attribute duration = read.openAttribute("duration");
			unsigned int size;
			duration.read(PredType::STD_U32LE, &size);

			// Open read raw data
			DataSet dataset = read.openDataSet("Signal");
			DataSpace dataspace = dataset.getSpace();

			// Check file consistency
			int rank = dataspace.getSimpleExtentNdims();
			if (rank != 1) {
				cerr << "ERROR: fast5 signal data is not 1D." << endl;
				exit(1);
			}
			hsize_t dims;
			dataspace.getSimpleExtentDims(&dims, NULL);
			if (dims != size) {
				cerr << "FAST5 ERROR: raw data length does not match duration attribute" << endl;
				exit(1);
			}

			// Read in raw data
			RawData.resize(size);
			dataset.read(RawData.data(), PredType::STD_I16LE);

			// Obtain the normalized signal for decoding 
			Signal::Normalize(signal, RawData, 8192*8, signal_levels_, low_clip_, high_clip_);

			// Prepare for the next signal or new file if nessessary
			read_number_++;
			if (read_number_ == num_reads_) {
				read_number_ = 0;
				delete h5_file_;
				h5_file_ = nullptr;
				file_queue_.pop();
			}

			// Write could slow speed of processing
			clog << "Read signal " << read_number_ + 1 << " of " << num_reads_ << " with duration " << size << " from '" << fname << "'" << endl;

		}
		catch (const H5::FileIException) {
			cerr << "ERROR: unable to open fast5 file '" << fname << "'" << endl;
			exit(1);
		}
		catch (const H5::Exception) {
			cerr << "ERROR: unable to parse fast5 file '" << fname << "'" << endl;
			exit(1);
		}

	}
}
