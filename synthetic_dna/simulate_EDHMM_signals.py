#!/usr/bin/env python -W ignore::DeprecationWarning
import sys
import numpy as np
import threading
import argparse
from fast5_research import extract
from tqdm import tqdm
import h5py
from uuid import uuid4
base_dict = {'A': 0, 'C': 1, 'G': 2, 'T': 3, 'a': 0, 'c': 1, 'g': 2, 't': 3}
base_dict_op = {0:'A', 1:'C', 2:'G', 3:'T'}
class Model:
    def __init__(self,model_path):
        f = h5py.File(model_path,'r')
        self.normal_high = f['Parameters']['Normalization'].attrs['HighClip']
        self.normal_low =  f['Parameters']['Normalization'].attrs['LowClip']
        self.signal_n = f['Parameters']['Normalization'].attrs['SignalLevels']
        self.signal_n = f['Tables']['ObservationProbabilities'].shape[0]
        self.observation = f['Tables']['ObservationProbabilities'][:]
        self.kmer = (np.log2(f['Tables']['ObservationProbabilities'].shape[1])/2).astype(int)
        self.D = f['Tables']['DurationProbabilities'].shape[0]
        self.tail_factor = f['Tables']['DurationProbabilities'].attrs['TailFactor']
        self.duration = f['Tables']['DurationProbabilities'][:]
        self.duration[-1] = self.duration[-1]*(1-self.tail_factor)
        self.middlek = int(self.kmer//2)
        f.close()
def base2kmer(Z,K):
    T = len(Z)
    Z_kmer = np.zeros(T-K+1)
    for i in range(T-K+1):
        Z_kmer[i]=base2num(Z[i:i+K],K,0,1)[0]
    return Z_kmer.astype(np.int64)
def base2num(Z, K, op=False,flip=False):
  #import pdb;pdb.set_trace()
  # for transfer base to indx
  if not op:
    #print('\n transfering base to indx...\n ')
    if type(Z) != list:
      if type(Z) == np.ndarray:
        Z = Z.tolist()
      else:
        Z = list([Z])
    T = len(Z)
    Z_ = np.zeros(T)  
    for i in range(T):
      kmer = Z[i]
      indx = 0
      for j in range(K-1,-1,-1):
        if flip:
          indx += base_dict[kmer[j]]*(4**j)
        else:
          indx += base_dict[kmer[K-1-j]]*(4**j)
      Z_[i] = indx
    Z_ = Z_.astype(int)
  else:
    #print('\n transfering indx to base...\n ')
    if type(Z) != list:
      if type(Z) == np.ndarray:
        Z = Z.tolist()
      else:
        Z = list([Z])
    T = len(Z)
    Z_ = list()
    for i in range(T):
      kmer = Z[i]
      base = None
      for j in range(K-1,-1,-1):
        indx = kmer//(4**j)
        kmer = kmer%(4**j)
        if not base:
          base = base_dict_op[indx]
          continue
        base += base_dict_op[indx] 
      Z_.append(base)
    if flip:
      for i in range(len(Z_)):
        Z_[i] = Z_[i][::-1]
    if K == 1:
      Z_ = ''.join(map(str,Z_))
    else:
      Z_ = np.asarray(Z_)
    #import pdb;pdb.set_trace()
  return Z_
##############################################################################
def str2float(string):
    try:
        return float(string)
    except ValueError:
        num, denom = string.split('/')
        frac = float(num) / float(denom)
        return frac
def str2bool(v):
    if v.lower() in ('yes', 'True','true', 't', 'y', '1'):
        return True
    elif v.lower() in ('no','Flase', 'false', 'f', 'n', '0'):
        return False
    else:
        raise argparse.ArgumentTypeError('Boolean value expected.')
def parse_arguments(sys_input):
    parser = argparse.ArgumentParser()
    parser.add_argument('-ref','--reference_file',default='./fakereference1000.fa',help='file contains the fake references')
    parser.add_argument('-reads_num',default=100,type=int,help='number of data points/sig_ref pairs to generate, default 100')
    parser.add_argument('-output',default='./data/',type=str,help='where to write output files, default ./data/')
    parser.add_argument('-model',default='',help='the paramter file contains observation table')
    parser.add_argument('-poisson',default=8,type=int,help='poisson distribution used as EDHMM duration, default 8, if set to 0 then use the duration table in model file instead')
    parser.add_argument('-p',type=int,default=2,help='number of threads to run in parallel, default 2')
    return parser.parse_args(sys_input)
def get_params():
    PARAMS = parse_arguments(sys.argv[1:])
    if not PARAMS.output[-1] =='/':
        PARAMS.output += '/'
    PARAMS.mapped = PARAMS.output+PARAMS.reference_file[:PARAMS.reference_file.rfind('.')]+'_mapped.hdf5'
    return PARAMS
#############################################################################
def digitize_write(raw_data,read_id,params):
    # np.int16 is required, the library will refuse to write anything other
    #read_idx = int(read_id[8:])
    digitisation = 8192.0
    start, stop = int(min(raw_data - 1)), int(max(raw_data + 1))
    rng = stop - start
    #bins = np.arange(start, stop, rng / digitisation)
    #raw_data = np.digitize(raw_data, bins).astype(np.int16)
    #raw_data = np.round(raw_data)
    raw_data = raw_data.astype(np.int16)
    # The following are required meta data
    channel_id = {
        'digitisation': digitisation,
        'offset': 0,
        'range': rng,
        'sampling_rate': 4000,
        'channel_number': 1,
    }
    read_id = {
        'start_time': 0,
        'duration': len(raw_data),
        'read_number': 1,
        'start_mux': 1,
        'read_id': str(read_id),
        'scaling_used': 1,
        'median_before': 0,
    }
    tracking_id = {
        'exp_start_time': '1970-01-01T00:00:00Z',
        'run_id': str(uuid4()).replace('-',''),
        'flow_cell_id': 'FAH00000',
    }
    context_tags = {}
    read = extract.Read(read_id,0,tracking_id=tracking_id, context_tags=context_tags, channel_id=channel_id,raw=raw_data)
    return read
def signaling(reference,read_id,params,hmm,mapped_reads,fast5_writer,locking):
    signals = list()
    kmers = base2kmer(reference,hmm.kmer)
    ref = base2num(list(reference),1,0,1)
    ref_len = len(kmers)
    duration_n = generate_duration(params,hmm,ref_len)
    ref_to_signal = np.zeros(ref_len+1).astype(np.int64)
    signals.append(np.random.choice(np.arange(hmm.signal_n),size=duration_n[0],p=hmm.observation[:,kmers[0]]))
    for i in range(1,ref_len):
        ref_to_signal[i] = ref_to_signal[i-1]+duration_n[i-1]
        signals.append(np.random.choice(np.arange(hmm.signal_n),size=duration_n[i],p=hmm.observation[:,kmers[i]]))
    ref_to_signal[-1] = ref_to_signal[-2]+duration_n[-1]
    signals = np.concatenate(signals)
    read = digitize_write(signals,read_id,params)
    with locking:
        fast5_writer.write_read(read)
        mread = mapped_reads.create_group(read_id)
        mread.create_dataset('Dacs',data=signals.astype(np.int16))
        mread.create_dataset('Reference',data=ref[hmm.middlek:-hmm.middlek].astype(np.int64))
        mread.create_dataset('Ref_to_signal',data=ref_to_signal.astype(np.int64))
def generate_duration(params,hmm,length):
    if params.poisson>0:
        duration_n = np.random.poisson(params.poisson,length)+1
    else:
        duration_n = np.random.choice(np.arange(1,len(d_prob)+1),length,p=hmm.duration)
    return duration_n
if __name__ == '__main__':
    '''
    input args:
    -references: sequences of DNA to generate signals from;
    -output: directory, probably don't want spamming the current folder with 10000 files
    -reads_num: reclaim to samller size of signals
    -model: model file to generate signals from.
    '''
    locking = threading.Lock()
    params = get_params()
    #kmer_means = signal_mean(params.kernel,params.kmer)
    thread_n = params.p
    hmm = Model(params.model)
    if params.poisson>0:
        hmm.duration = np.random.poisson(params.poisson,30)
    mapped_f = h5py.File(params.mapped,'w')
    mapped_reads = mapped_f.create_group('Reads')
    references_f = open(params.reference_file,'r')
    fast5_writer = extract.MultiWriter(params.output,by_id=False,reads_per_file=params.reads_num)
    reference = ''
    refers_count = 0
    threads = list()
    pbar = tqdm(total=params.reads_num)
    for lines in references_f:
        line = lines.strip().split('\t')
        if '>' in lines or '@' in lines: # means at begining of a new read/sequence
            if refers_count<0:
                refers_count += 1
                read_id = line[0][1:]
                continue
            if len(reference)>10000: # too long 
                reference = ''
                continue
            if len(reference) > 0: # deal with last read
                refers_count += 1
                threads.append(threading.Thread(target=signaling,args=(reference,read_id,params,hmm,mapped_reads,fast5_writer,locking,)))
                if len(threads) == thread_n:
                    for j in range(thread_n):
                        threads[j].start()
                    for j in range(thread_n):
                        threads[j].join()
                        pbar.update(1)
                    threads = list()
                    if refers_count >= params.reads_num:
                        break
                reference = ''
                read_id = line[0][1:]
            else:
                read_id = line[0][1:]
        else:
            reference += line[0]
    if len(threads) > 0:
        for j in range(thread_n):
            threads[j].start()
        for j in range(thread_n):
            threads[j].join()
            pbar.update(1)
    print("reference count: "+str(refers_count))
