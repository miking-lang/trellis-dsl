import sys
import numpy as np
import params_parse
import threading
from utils_dna import base2num, A_kmer,base_only_assembly, transition_compute
from tqdm import tqdm
def random_cut(reference,output_f,cut_range,id_num,locking):
    length = int(np.random.uniform(cut_range[0],cut_range[1]))
    start = int(np.random.uniform(0,len(reference)-length))
    with locking:
        output_f.write('>catitude'+str(id_num)+'\n')
        output_f.write(reference[start:start+length]+'\n')
#        for i in range(length//60+2):
#            output_f.write(reference[start+i*60:start+(i+1)*60]+'\n')
def fake_genome(length,transition,kmer):
    refer_idx = np.zeros(length,dtype=int)
    transit_kmer = A_kmer(kmer)
    transit_kmer = transit_kmer.astype(int)
    transit_p = make_transition(length,transition,kmer)
    transit_p = transit_p/transit_p.sum(axis=1)[:,None]
    refer_idx[0] = int(np.random.randint(0,4**kmer))
    for i in tqdm(range(1,length)):
        nextb = np.random.choice(np.arange(4), 1, p=transit_p[refer_idx[i-1],:])
        refer_idx[i] = int(transit_kmer[refer_idx[i-1],nextb])
    #A_hat = transition_compute(refer_idx,kmer)
    #import pdb;pdb.set_trace()
    reference = base_only_assembly(refer_idx,kmer)
    return reference
def make_transition(length,transition,kmer):
    trans_p = np.zeros((4**kmer,4))
    if "unif" in transition:
        trans_p += np.array([1/4, 1/4, 1/4, 1/4])
    elif "norm" in transition:# raughly a normal
        trans_p += np.array([0.15,0.35,0.35,0.15])
    elif 'rand' in transition: # randomly generate for each kmer
        trans_p = np.random.rand(4**kmer,4)
        np.savetxt('random_transition_probability.txt',trans_p,delimiter=', ')
    return trans_p
if __name__=='__main__':
    '''
    some choice to make
    arguments:
    -kmer: general parameter
    -transition: distribution choice, MUST have value if faking genome
    -genome_file: where the genome is stored if use real genome file
    -genome_length:  the length of the fake genome
    -reads_num: number of cuts
    -references: output files stored the chopped references
    -cut_range: length range of the chopped references [3000,20000]
    output references.fa and fake_trans_genomeK.fa if requested
    '''
    lock = threading.Lock()
    params = params_parse.get_ref_params()
    import pdb;pdb.set_trace()
    reference = ''
    refers_count = 0
    output_f = open(params.references_file,'w')
    threads = list()
    if len(params.trans) > 0: #create fake genome according to certain transition matrix
        print('generating genome and reference')
        reference = fake_genome(params.genome_length,params.trans,params.kmer)
        fake_genome_f = open('fakegenome_'+params.trans+str(params.kmer)+'.fa','w')
        fake_genome_f.write('>fake_genome\n')
        for i in range(len(reference)//80+1):
            fake_genome_f.write(reference[i*80:(i+1)*80])
            fake_genome_f.write('\n')
        #fake_genome_f.write(reference) has to have a nice format, other wise Bio.SeqIO refuse to work
        fake_genome_f.close()
    else: #use the orginal DNA sequence
        print('generating reference from genome file')
        genome_f = open(params.genome_file,'r')
        for lines in genome_f:
            line = lines.strip().split('\t')
            if '>' in lines or '@' in lines: # means at begining of a new read/sequence
                if len(reference) > 0:
                    for i in range(params.reads_num):
                        refers_count += 1
                        threads.append(threading.Thread(target=random_cut,args=(reference,output_f,params.cut_range,refers_count,lock,)))
                    reference = ''
                else:
                    reference += line[0]
            else:
                reference += line[0]
    for i in range(params.reads_num):
        refers_count += 1
        threads.append(threading.Thread(target=random_cut,args=(reference,output_f,params.cut_range,refers_count,lock,)))
    for i in tqdm(range(len(threads))):
        threads[i].start()
    for i in range(len(threads)):
        threads[i].join()
    output_f.close()
