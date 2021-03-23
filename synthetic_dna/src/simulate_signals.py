import sys
import numpy as np
import threading
import params_parse
from utils_dna import base2num, transferflip
from fast5_research import Fast5
from tqdm import tqdm
import tables
import scipy.stats as stats
from uuid import uuid4
import matplotlib.pyplot as plt
def digitize_write(raw_data,read_id,params):
    digitisation = 8192.0
    start, stop = int(min(raw_data - 1)), int(max(raw_data + 1))
    rng = stop - start
    bins = np.arange(start, stop, rng / digitisation)
    # np.int16 is required, the library will refuse to write anything other
    #raw_data = np.digitize(raw_data, bins).astype(np.int16)
    raw_data = np.round(raw_data)
    raw_data = raw_data.astype(np.int16)
    filename = params.fast5_path+read_id+'.fast5'
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
def signaling(reference,read_id,means,duration_f,params,locking):
    signals = list()
    ref_len = len(reference)
    duration_n = generate_duration(params.duration,ref_len-params.kmer+1)
    with locking:
        duration_f.write(read_id)
        duration_f.write('\n')
        duration_f.write(" ".join(map(str, duration_n)))
        duration_f.write('\n')
    base_n = base2num(reference[:params.kmer],params.kmer)[0]
    signals = np.random.normal(means[base_n],params.variance,duration_n[0])
    for i in range(1,ref_len-params.kmer+1):
        base_n = base2num(reference[i:i+params.kmer],params.kmer)[0]
        signals = np.concatenate((signals,np.random.normal(means[base_n],params.variance,duration_n[i])))
    digitize_write(signals,read_id,params)
def generate_duration(duration,length):
    if 'pois' in duration:
        try:
            lam = int(duration[-1])
        except ValueError:
            lam = 8
        duration_n = np.random.poisson(lam,length)
        duration_n[duration_n==0] = lam
    else:
        d_prob = np.array([0.0226, 0.0445,0.0804,0.1036,0.1086,0.1021,0.0900,0.0768,0.0642,0.0530,0.0434,0.0355,0.0289,0.0236,0.0194,0.0159,0.0131,0.0109,0.0090,0.0075,0.0063,0.0053,0.0045,0.0038,0.0032,0.0028,0.0024,0.0020,0.0018,0.0015,0.0013,0.0012,0.0010,0.0009,0.0008,0.0007,0.0006,0.0006,0.0005,0.0004,0.0004,0.0004,0.0003,0.0003,0.0003,0.0002,0.0002,0.0002,0.0002,0.0002,0.0002,0.0002,0.0001,0.0001,0.0001,0.0001,0.0001,0.0001,0.0001,0.0001,0.0001,0.0001,0.0002,0.0011])
        duration_n = np.random.choice(np.arange(1,len(d_prob)+1),length,p=d_prob)
    if params.duration_cap > 0:
        duration_n[duration_n>=params.duration_cap] = lam
    return duration_n
def signal_mean(kernel,kmer,bmean={'G':12,'A':25,'C':75,'T':88}):
    #kernel = kernel/sum(kernel)
    means = np.zeros(4**kmer)
    for i in range(4**kmer):
        bases = base2num(i,kmer,op=True)[0]
        for j in range(kmer):
            means[i] += kernel[j]*bmean[bases[j]]
    return means
def write_params(kmer_means,params):
    param_f = tables.open_file(params.params_file,'r+')
    try:
        param_f.root.Tables.DurationProbabilities.remove()
    except:
        pass
    try:
        param_f.root.Tables.ObservationProbabilities.remove()
    except:
        pass
    try:
        param_f.root.Tables.TransitionProbabilities.remove()
    except:
        pass
    import pdb;pdb.set_trace()
    if 'unif' in params.references_file:
        param_f.create_array(param_f.root.Tables,'TransitionProbabilities',obj=np.ones((4,4**params.kmer))*0.25)
    elif 'norm' in params.references_file:
        param_f.create_array(param_f.root.Tables,'TransitionProbabilities',obj=np.zoes((4,4**params.kmer))+np.array([0.15,0.35,0.35,0.15]).reshape(-1,1))
    else:
        print('ERROR: do not support random transition')
        sys.exit(1)
    if 'pois' in params.duration:
        try:
            lamb = int(params.duration[-1])
            param_f.create_array(param_f.root.Tables,'DurationProbabilities',obj=stats.poisson.pmf(np.arange(16),lamb))
        except:
            param_f.create_array(param_f.root.Tables,'DurationProbabilities',obj=stats.poisson.pmf(np.arange(16),8))
    else:
        print('ERROR: do not support random duration')
        sys.exit(1)
    K = 4**params.kmer
    flip_kmer = transferflip(np.arange(K),params.kmer)
    new_observ = np.zeros((100,K))
    for i in range(K):
        new_observ[:,flip_kmer[i]] = stats.norm.pdf(np.arange(100),kmer_means[i],params.variance) # fixed for matching the bins structure of Joakim's
    #for i in range(K):
        #new_observ[int(kmer_means[i]),int(flip_kmer[i])] = 1
    import pdb;pdb.set_trace()
    param_f.create_array(param_f.root.Tables,'ObservationProbabilities',obj=new_observ)
    param_f.root.Parameters._v_attrs['KMerLength'] = params.kmer
    param_f.root.Tables.DurationProbabilities._v_attrs['TailFactor'] = 0.3
    param_f.root.Parameters._v_attrs['ExplicitDurationLength'] = 16
    param_f.root.Parameters.Normalization._v_attrs['SignalLevels'] = 100
    param_f.close()
if __name__ == '__main__':
    '''
    input args:
    -kmer: general parameter
    -references: singals with generated from references
    -kernel: filter to generate observation table means, need to be vector with size kmer
    -duration: duration probabilities, format 'poissonLamda', e.g poisson5
    -var: variance for normal observation talve
    -fast5_path: directory, probably don't want spamming the current folder with 10000 files
    -params_file: store parameters for testing 
    -duration_cap: for limited durations
    -reads_num: reclaim to samller size of signals
    '''
    thread_n = 200
    locking = threading.Lock()
    params = params_parse.get_sig_params()
    import pdb;pdb.set_trace()
    kmer_means = signal_mean(params.kernel,params.kmer)
    import pdb;pdb.set_trace()
    write_params(kmer_means,params)
    import pdb;pdb.set_trace()
    duration_f = open('durations.txt','w')
    references_f = open(params.references_file,'r')
    reference = ''
    refers_count = 0
    threads = list()
    for lines in references_f:
        line = lines.strip().split('\t')
        if '>' in lines or '@' in lines: # means at begining of a new read/sequence
            if len(reference) > 0:
                refers_count += 1
                threads.append(threading.Thread(target=signaling,args=(reference,read_id,kmer_means,duration_f,params,locking,)))
                if len(threads) == thread_n:
                    for j in range(thread_n):
                        threads[j].start()
                    for j in range(thread_n):
                        threads[j].join()
                    threads = list()
                    print(str(refers_count))
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
    print("reference count: "+str(refers_count))
    references_f.close()
    duration_f.close()
    import pdb;pdb.set_trace()    
