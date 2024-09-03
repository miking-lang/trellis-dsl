
#include "model.h"
#include "math.h"

#include <iostream>
#include <string>
using namespace std;

#include<H5Cpp.h>
using namespace H5;

static
H5E_auto_t func(void* client_data) {

	cerr << "Finally here!" << endl;

}

ViterbiModel::ViterbiModel(const string &model) :
	ObservationTable(NULL),
	ExplicitDurationTable(NULL),
	TransitionTable(NULL)
{
	//H5::Exception::dontPrint(); // Turn of the H5 C routine error stack messages for cleaner user feedback
	try {
		// Open HDF5 file with trained model
		H5File file(model, H5F_ACC_RDONLY);

		// Obtain model parameters
		{
			Group params = file.openGroup("Parameters");
			Attribute klen = params.openAttribute("KMerLength");
			klen.read(PredType::STD_U32LE, &KmerLength);
			Attribute dlen = params.openAttribute("ExplicitDurationLength");
			dlen.read(PredType::STD_U32LE, &DurationLength);

			Group norm = params.openGroup("Normalization");
			Attribute slev = norm.openAttribute("SignalLevels");
			slev.read(PredType::STD_U32LE, &SignalLevels);
			Attribute lclip = norm.openAttribute("LowClip");
			lclip.read(PredType::IEEE_F32LE, &LowClip);
			Attribute hclip = norm.openAttribute("HighClip");
			hclip.read(PredType::IEEE_F32LE, &HighClip);
		}

		// Get number of bits in duation
		{
			unsigned int dm = DurationLength;
			DurationBits = 0;
			while ((dm & 0x01) == 0) {
				dm >>= 1;
				DurationBits++;
			}
			if ((dm >> 1) != 0) {
				cerr << "ERROR: only duration tables of length 2^p are currently supported!" << endl;
				exit(1);
			}
		}
		unsigned int TotalKmers = 1 << (2 * KmerLength); // Assumes kBitsPerBase = 2

		// Read lookup table data
		Group tables = file.openGroup("Tables");
		// Input data related to duration table
		{
			DataSet durations = tables.openDataSet("DurationProbabilities");
			DataSpace table = durations.getSpace();
			int rank = table.getSimpleExtentNdims();
			if (rank != 1) {
				cerr << "ERROR: duration table of incorrect dimension" << endl;
				exit(1);
			}
			hsize_t dims[1];
			table.getSimpleExtentDims(dims);
			if (dims[0] != DurationLength) {
				cerr << "ERROR: size of duration table does not match model parameters" << endl;
				exit(1);
			}
			ExplicitDurationTable = new float[DurationLength];
			durations.read(ExplicitDurationTable, PredType::IEEE_F32LE);
			Attribute tailprobability = durations.openAttribute("TailFactor");
			tailprobability.read(PredType::IEEE_F32LE, &TailFactor); // Fix this som model.cpp is the same for both training and decoding
		}

		// Input data related to observation table
		{
			DataSet observations = tables.openDataSet("ObservationProbabilities");
			DataSpace table = observations.getSpace();
			int rank = table.getSimpleExtentNdims();
			if (rank != 2) {
				cerr << "ERROR: incorrect formatting of observation table" << endl;
				exit(1);
			}
			hsize_t dims[2];
			table.getSimpleExtentDims(dims);
			if ((dims[0] != SignalLevels) || (dims[1] != TotalKmers)) {
				cerr << "ERROR: size of observation table does not match model parameters" << endl;
				exit(1);
			}
			ObservationTable = new float[SignalLevels * TotalKmers];
			observations.read(ObservationTable, PredType::IEEE_F32LE);
		}

		// Input data related to transition table
		{
			DataSet transitions = tables.openDataSet("TransitionProbabilities");
			DataSpace table = transitions.getSpace();
			int rank = table.getSimpleExtentNdims();
			if (rank != 2) {
				cerr << "ERROR: incorrect formatting of transition table" << endl;
				exit(1);
			}
			hsize_t dims[2];
			table.getSimpleExtentDims(dims);
			if ((dims[0] != 4) || (dims[1] != TotalKmers)) {
				cerr << "ERROR: size of transition table does not match model parameters" << endl;
				exit(1);
			}
			TransitionTable = new float[4 * TotalKmers];
			transitions.read(TransitionTable, PredType::IEEE_F32LE);
		}

		clog << "Loaded the Viterbi model." << endl;
	}
	catch (const H5::FileIException) {
		cerr << "ERROR: unable to open parameter file '" << model << "'" << endl;
		exit(1);
	}
	catch (const H5::Exception) {
		cerr << "ERROR: unable to parse parameter file '" << model << "'" << endl;
		exit(1);
	}
	catch (bad_alloc &e) {
		cerr << "\t" << e.what() << endl;
		cerr << "ERROR: unable to allocate memory for Viterbi model" << endl;
		exit(1);
	}
}

ViterbiModel::~ViterbiModel()
{
	if (ExplicitDurationTable != NULL) delete ExplicitDurationTable;
	if (ObservationTable != NULL) delete ObservationTable;
	if (TransitionTable != NULL) delete TransitionTable;
};


void
ViterbiModel::Logarithmic() {

	// Convert tail factor to log-scale
	ExplicitDurationTable[DurationLength - 1] *= (1 - TailFactor); // Add early dropout probability
	DurationTailExponent = log(TailFactor);

	unsigned int TotalKmers = 1 << (2 * KmerLength); // Assumes kBitsPerBase = 2

	// Convert lookup tables to log-scale
	for (unsigned int n = 0; n < DurationLength; n++) {
		ExplicitDurationTable[n] = log(ExplicitDurationTable[n]);
	}
	for (unsigned int n = 0; n < SignalLevels * TotalKmers; n++) {
		ObservationTable[n] = log(ObservationTable[n]);
	}
	for (unsigned int n = 0; n < 4 * TotalKmers; n++) {
		TransitionTable[n] = log(TransitionTable[n]);
	}

};

void
ViterbiModel::SaveModel(const string& model)
{
	try {
		// Open HDF5 file to save model
		H5File file(model, H5F_ACC_TRUNC);

		// Save model parameters
		{
			Group params(file.createGroup("Parameters"));
			DataSpace sdataspace(0, NULL); // Scalar dataspace

			// Write general attributes
			Attribute klen = params.createAttribute("KMerLength", PredType::STD_U32LE, sdataspace);
			klen.write(PredType::STD_U32LE, &KmerLength);
			Attribute dlen = params.createAttribute("ExplicitDurationLength", PredType::STD_U32LE, sdataspace);
			dlen.write(PredType::STD_U32LE, &DurationLength);

			Group norm = params.createGroup("Normalization");
			Attribute slev = norm.createAttribute("SignalLevels", PredType::STD_U32LE, sdataspace);
			slev.write(PredType::STD_U32LE, &SignalLevels);
			Attribute lclip = norm.createAttribute("LowClip", PredType::IEEE_F32LE, sdataspace);
			lclip.write(PredType::IEEE_F32LE, &LowClip);
			Attribute hclip = norm.createAttribute("HighClip", PredType::IEEE_F32LE, sdataspace);
			hclip.write(PredType::IEEE_F32LE, &HighClip);
		}

		// Save lookup table data
		Group tables = file.createGroup("Tables");
		// Save data related to duration table
		{
			hsize_t dims[1];
			dims[0] = DurationLength;
			DataSpace table(1, dims);
			DataSet durations = tables.createDataSet("DurationProbabilities", PredType::IEEE_F32LE, table);
			durations.write(ExplicitDurationTable, PredType::IEEE_F32LE);

			DataSpace sdataspace(0, NULL); // Scalar dataspace
			Attribute tailprobability = durations.createAttribute("TailFactor", PredType::IEEE_F32LE, sdataspace);
			tailprobability.write(PredType::IEEE_F32LE, &TailFactor);
		}

		// Save data related to observation table
		{
			hsize_t dims[2];
			dims[0] = SignalLevels;
			unsigned int TotalKMers = 1 << (2 * KmerLength); // Assumes kBitsPerBase = 2
			dims[1] = TotalKMers;
			DataSpace table(2, dims);
			DataSet observations = tables.createDataSet("ObservationProbabilities", PredType::IEEE_F32LE, table);
			observations.write(ObservationTable, PredType::IEEE_F32LE);
		}

		// Save data related to transition table
		{
			hsize_t dims[2];
			dims[0] = 4; // Number of bases, assumes kBitsPerBase = 2
			unsigned int TotalKMers = 1 << (2 * KmerLength); // Assumes kBitsPerBase = 2
			dims[1] = TotalKMers;
			DataSpace table(2, dims);
			DataSet observations = tables.createDataSet("TransitionProbabilities", PredType::IEEE_F32LE, table);
			observations.write(TransitionTable, PredType::IEEE_F32LE);
		}

	}
	catch (const H5::Exception) {
		cerr << "ERROR: unable to save parameter file '" << model << "'" << endl;
	}
}
