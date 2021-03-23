import numpy as np
import sys
import argparse

np.set_printoptions(threshold=sys.maxsize)
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
def take_from_command():
    args = parser.parse_args(sys.argv[1:])
    return args
def get_ref_params():
    # need to do some check and announcement
    if len(PARAMS.trans) == 0: #means to use real genome
        print('using real genome at '+PARAMS.genome_file+'...')
    else:
        print('creating fake DNA-sequence of length '+str(PARAMS.genome_length)+' with '+PARAMS.trans+' distribution for '+str(PARAMS.kmer)+' kmer...' )
        PARAMS.references_file = 'fake_'+PARAMS.trans+str(PARAMS.kmer)+'_'+PARAMS.references_file
    return PARAMS
def get_sig_params():
    if len(PARAMS.fast5_path) == 0:
        print('ERROR: must save fast5 files in a seperate folder!')
        sys.exit(1)
    else:
        if PARAMS.fast5_path[-1] != '/':
            PARAMS.fast5_path = PARAMS.fast5_path + '/'
    if len(PARAMS.kernel) == PARAMS.kmer:
        print('simulating signals using reference from '+PARAMS.references_file+' with duration: '+PARAMS.duration+ ' output in '+PARAMS.fast5_path)
        PARAMS.kernel = np.asarray(PARAMS.kernel)
        PARAMS.kernel = PARAMS.kernel/sum(PARAMS.kernel)
        return PARAMS
    else:
        print('ERROR: kernel has to have same length as kmer!')
        sys.exit(1)
parser = argparse.ArgumentParser()

# general arg
parser.add_argument('-kmer',default=5,type=int,help='kmer number to use in general')
parser.add_argument('-references','--references_file',default='references.fa',help='output file for storing the splited sequences')

# args for simulate_references
parser.add_argument('-transition','--trans', default='',help='distribution choise for transition probability, if not input then use the real DNA in genome.fa')
parser.add_argument('-genome_length', default=4000000,type=int,help='the length of faked DNA sequence')

parser.add_argument('-genome_file',default='genome.fa',help='file contains DNA sequence, in simulate_references only used if none transition distribution is given')
parser.add_argument('-reads_num',default=1000,type=int,help='number of data points/sig_ref pairs to generate')
parser.add_argument('-cut_range',nargs=2,type=int,default=[300,1000])

# args for simulate_signals
parser.add_argument('-kernel',nargs='*',type=str2float,default=[1,2,3,3,1],help='the weights/kernel used for generating fake signals, has to have same length of kmer')
parser.add_argument('-duration',type=str,default='poisson',help='the duration probabilities')
parser.add_argument('-var','--variance',type=float,default=0.1,help='variance of oberservation')
parser.add_argument('-fast5_path',type=str)
parser.add_argument('-params_file',default='Params_fakegenome.h5',help='store corresponding parameters')
parser.add_argument('-duration_cap',default=0,type=int,help='the duration is limited to a certain number if not 0')
if __name__=='__main__':
    PARAMS = take_from_command()
    import pdb; pdb.set_trace()
else:
    PARAMS = take_from_command()
