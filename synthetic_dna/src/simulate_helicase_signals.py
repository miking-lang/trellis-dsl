import sys
import numpy as np
import threading
import argparse
from fast5_research import Fast5
from tqdm import tqdm
import h5py
from uuid import uuid4
import matplotlib.pyplot as plt
base_dict = {'A': 0, 'C': 1, 'G': 2, 'T': 3, 'a': 0, 'c': 1, 'g': 2, 't': 3}
class Model:
    def __init__(self,model_path):
        f = h5py.File(model_path,'r')
        self.normal_high = f['Parameters']['Normalization'].attrs['HighClip']
        self.normal_low =  f['Parameters']['Normalization'].attrs['LowClip']
        self.signal_n = f['Parameters']['Normalization'].attrs['SignalLevels']
        self.h_n = f['Tables']['InnerTransitionProbabilities'].shape[0]
        self.kmer = (np.log2(f['Tables']['ObservationProbabilities'].shape[1]/self.h_n)/2).astype(int)
        self.observation = f['Tables']['ObservationProbabilities'][:]
        self.innertransition = f['Tables']['InnerTransitionProbabilities'][:]
        self.transition = f['Tables']['TransitionProbabilities'][:]
        f.close()
def base2kmer(Z,K,num_op=True):
    T = len(Z)
    Z_kmer = np.zeros(T-K+1)
    for i in range(K,T+1):
        Z_kmer[i-K]=base2num(Z[i-K:i],K,flip=1)[0]
    return Z_kmer.astype(np.int)
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
    if K == 1:
      Z_ = ''.join(map(str,Z_))
    else:
      Z_ = np.asarray(Z_)
    #import pdb;pdb.set_trace()
  return Z_
def transferflip(base_i,K):
  # take in a array of base_idx and flip the coding rule
  flip_i = base2num(base2num(base_i,K,op=True),K,flip=True)
  return flip_i
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
    parser.add_argument('-references','--references_file',default='./fake_unif5_references_new.fa',help='fasta file for storing the splited sequences')
    parser.add_argument('-reads_num',default=1000,type=int,help='number of data points/sig_ref pairs to generate')
    parser.add_argument('-output',default='',type=str)
    parser.add_argument('-model',default='',help='the paramter file')
    parser.add_argument('-p',type=int,default=10,help='number of threads to run in parallel')
    return parser.parse_args(sys_input)
def get_params():
    PARAMS = parse_arguments(sys.argv[1:])
    if len(PARAMS.output) == 0:
        print('ERROR: must save fast5 files in a seperate folder!')
        sys.exit(1)
    else:
        if PARAMS.output[-1] != '/':
            PARAMS.output = PARAMS.output + '/'
    print('simulating '+str(PARAMS.reads_num)+' signals using reference from '+PARAMS.model+' in '+PARAMS.output)
    return PARAMS
def digitize_write(raw_data,read_id,params):
    # np.int16 is required, the library will refuse to write anything other
    digitisation = 8192.0
    start, stop = int(min(raw_data - 1)), int(max(raw_data + 1))
    rng = stop - start
    #bins = np.arange(start, stop, rng / digitisation)
    #raw_data = np.digitize(raw_data, bins).astype(np.int16)
    #raw_data = np.round(raw_data)
    raw_data = raw_data.astype(np.int16)
    filename = params.output+read_id+'.fast5'
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
    with Fast5.New(filename, 'w', tracking_id=tracking_id, context_tags=context_tags, channel_id=channel_id) as h:
        h.set_raw(raw_data, meta=read_id, read_number=1)
def signaling(reference,read_id,hmm,duration_f,params,locking):
    signals = list()
    ref_len = len(reference)
    kmers = base2kmer(reference,hmm.kmer)
    signal_read = []
    inner_read = []
    pbar = tqdm(total=len(kmers))
    for kmer in kmers:
        pbar.update(1)
        signal = -1
        inner_t = -1
        observ_start = kmer*hmm.h_n
        while(inner_t<3):
            inner_t = np.random.choice(np.arange(hmm.h_n),p=hmm.innertransition[:,inner_t])
            signal = np.random.choice(np.arange(hmm.signal_n),p=hmm.observation[:,observ_start+inner_t])
            inner_read.append(inner_t)
            signal_read.append(signal)
    signal_read = np.asarray(signal_read)
    pbar.close()
    with locking:
        duration_f.write(read_id)
        duration_f.write('\n')
        duration_f.write(" ".join(map(str, inner_read)))
        duration_f.write('\n')
    digitize_write(signal_read,read_id,params)
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
    duration_f = open(params.output+'innerstates.txt','w')
    references_f = open(params.references_file,'r')
    reference = ''
    refers_count = 0
    threads = list()
    pbar = tqdm(total=params.reads_num)
    for lines in references_f:
        line = lines.strip().split('\t')
        if '>' in lines or '@' in lines: # means at begining of a new read/sequence
            if len(reference)>10000:
                reference = ''
                continue
            if len(reference) > 0:
                refers_count += 1
                threads.append(threading.Thread(target=signaling,args=(reference,read_id,hmm,duration_f,params,locking,)))
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
    references_f.close()
    duration_f.close()
