# in this script, K is kmer
import sys
import os
import matplotlib.pyplot as plt
import numpy as np
# import tables # do not involve if not needed
import params_parse
from tqdm import tqdm
np.set_printoptions(threshold=sys.maxsize)
base_dict_op = {0:'A', 1:'C', 2:'G', 3:'T'}
base_dict = {'A': 0, 'C': 1, 'G': 2, 'T': 3, 'a': 0, 'c': 1, 'g': 2, 't': 3}
def plot_list(l,ali=[],base='',max_plot = 20,save_fig=False):
  if type(l)==list:
    if len(l) < 20:
      max_plot = len(l)
    for i in range(max_plot):
      plt.figure()
      plt.plot(l[i])
      plt.xticks(ali[i],list(base[i]))
      plt.grid(True)
      if save_fig:
        fname = 'HMM_align_'+str(i)
        plt.savefig(PARAMS.savepath+fname,format='png')
      else:
        plt.draw()
        plt.pause(1) # <-------
        input('<Hit Enter To Close>')
  else:
    plt.figure()
    plt.plot(l) 
    plt.xticks(ali,list(base))
    plt.grid()
    if save_fig:
      fname = 'HMM_align_'+str(i)
      plt.savefig(PARAMS.savepath+fname,format='png')
    else:
      plt.draw()
      plt.pause(1) # <-------
      input('<Hit Enter To Close>')
  plt.close()
def A_init(K):#inital A with 0.25
  base_dict_op = {0:'A', 1:'C', 2:'G', 3:'T'}
  A = np.zeros((4**K,4**K))
  for i in range(4**K):
    base = base2num([i],K,op=True)[0]
    for j in range(4):
      indx = base2num([base[-K+1:]+base_dict_op[j]],K)
      A[i,indx] = 0.25
  return A
def A_kmer(K): # create array cotains 4 candidates each kmer can transite into
  base_dict_op = {0:'A', 1:'C', 2:'G', 3:'T'}
  A_kmer = np.zeros((4**K,4))
  for i in range(4**K):
    base = base2num([i],K,op=True)[0]
    for j in range(4):
      indx = base2num([base[-K+1:]+base_dict_op[j]],K)
      A_kmer[i,j] = indx
  return A_kmer
# calculate prior of X based on MLE
def prior_init(Z,K,mod='unit'):
  Po = np.ones(4**K)/4**K
  if mod=='unit':
    return Po
  if mod == 'random':
    Po = np.random.rand(4**K)
    Po = Po/Po.sum()
    return Po
  else:
    Z = Z.astype(int)
    T = len(Z)
    for t in range(T):
      Po[Z[t]] = Po[Z[t]]+1
    #import pdb; pdb.set_trace()
    row_sums = Po.sum()
    Po = Po/row_sums
    #print('the prior by MLE is:'+"\n"+str(Po))
    print('done')
    return Po
# calculate transition table based on MLE
def Pxz_init(K,bin_num=0):
  bin_num = int(bin_num)
  if bin_num != 0:
    Pxz = np.random.rand(4**K,bin_num)
    Pxz = np.divide(Pxz,np.sum(Pxz,axis=1).reshape(-1,1))
  return Pxz
def transition_compute(Z_,K):
  print('caluating transition matrix by MLE...')
  Z_ = Z_.astype(int)
  T = len(Z_)
  A = A_init(K)
  Zb = -1
  for t in range(T):
    Za = Z_[t]
    if Zb >= 0:
      A[Zb,Za] = A[Zb,Za]+1
      Zb = Za
    else:
      Zb = Za
      continue
    #if Za == 4**K-1 and Zb<252:
    #  print(Z)
    #  print(t)
  #import pdb; pdb.set_trace()
  A = A/A.sum(axis=1).reshape(-1,1)
  #A = A + np.diag(np.ones(4**K)*4/5)
  #print('the transition matrix by MLE is:'+"\n"+str(A))
  print('done')
  return A
###############################################################################################
def normalize(x,op='standarlise'):
  if op=='normalize':
    x_min = np.min(x)
    x_max = np.max(x)
    y = (x-x_min)/(x_max-x_min)
  if op=='standarlise':
    x_bar = np.mean(x)
    x_var = np.var(x)
    y = (x-x_bar)/np.sqrt(x_var)
  if op == 'median_win':
    med = np.median(x)
    MAD = np.median(np.absolute(x-med))
    x[x>med+5*MAD]=med+5*MAD
    x[x<med-5*MAD]=med-5*MAD
    y=(x-med)/MAD
  return y
def base2table(bases,k=4):
  if type(bases[0])==str:
    # from ACTG to one-hot-coding table of 0~4^k
    base_dict = {'A': 0, 'C': 1, 'G': 2, 'T': 3, 'a': 0, 'c': 1, 'g': 2, 't': 3}
    num_kmer = len(bases)
    output_idx = np.zeros((num_kmer,4**k))
    output_basenum = np.zeros(num_kmer)
    for j in range(num_kmer):
      kmer = bases[j]
      #print(kmer)
      indx = 0
      for i in range(k-1,-1,-1):
        indx += base_dict[kmer[k-1-i]]*4**i
      output_idx[j,int(indx)] = 1
      output_basenum[j] = indx
    return output_idx.astype(int), output_basenum  
  else:
    num_kmer = np.shape(bases)[0]
    bases = bases.reshape(num_kmer)
    output_idx = np.zeros((num_kmer,4**k))
    for j in range(num_kmer):
      output_idx[j,bases[j]] = 1
    return output_idx.astype(int)
def base2vec(bases,k=4):
  # from ACTG to one-hot-coding of 0~4*k
  base_dict = {'A': 0, 'C': 1, 'G': 2, 'T': 3, 'a': 0, 'c': 1, 'g': 2, 't': 3}
  num_kmer = len(bases)
  output_vec =np.zeros((num_kmer,k*4))
  for i in range(num_kmer):
    for j in range(k):
      output_vec[i,j*4+base_dict[bases[i][j]]] = int(1)
  #output_vec = int(output_vec)
  return output_vec.astype(int)
def base2kmer(Z,K,num_op=True):
  T = len(Z)
  Z_kmer = np.zeros(T-K+1)
  for i in range(K,T+1):
    Z_kmer[i-K]=base2num(Z[i-K:i],K)[0]
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
################################################################################################
def seg_assembler(base_list):
  T = len(base_list)
  max_len = len(max(base_list,key=len))
  ass = np.zeros((4,max_len*T))
  print('assembling segments')
  for i in tqdm(range(T-1)):
    matches = matcher(a=base_list[i],b=base_list[i+1])
    if i==0:
      Ta = len(base_list[i])
      Tb = len(base_list[i+1])
      Ia = base2num(list(base_list[i]),1)
      Ib = base2num(list(base_list[i+1]),1)
      match_idx = matches.find_longest_match(0,Ta,0,Tb)
      start_i = match_idx[0]-match_idx[1]
      ass[Ia,np.arange(Ta)] += 1
      ass[Ib,np.arange(Tb)+start_i] += 1
      Ta = Tb
    else:
      Tb = len(base_list[i+1])
      Ib = base2num(list(base_list[i+1]),1)
      match_idx = matches.find_longest_match(0,Ta,0,Tb)
      start_i += match_idx[0] - match_idx[1]
      ass[Ib,np.arange(Tb)+start_i] += 1
      Ta = Tb
    ass_nonzero = np.where(np.max(ass,axis=0)!=0)[0]
    ass_base = base2num(np.argmax(ass[:,ass_nonzero],axis=0),1,op=1)
  return ass_base
def assembler(Z_idx,Z_base,kmer,start=0):
  # the input has to include the duration information as well
  repeat_idx = np.zeros(4)
  for i in range(4):
    for j in range(kmer):
      repeat_idx[i] += i*(4**j)
  repeat_base = base2num(repeat_idx,kmer,op=True) # only care about 'AAA' 'CCC' 'GGG' 'TTT'
  #print(repeat_test)
  T = len(Z_idx)
  base = ''
  repeat = 0
  for i in range(T):
    #isspecial = len(np.where(repeat_test==Z_idx[i])[0])>0
    if len(base)==0:
      base = base + Z_base[i][start:]
      '''
    elif Z_idx[i-1]==Z_idx[i]:# only care about 'AAA' 'CCC' 'GGG' 'TTT'
      if Z_base[i] in repeat_base:
        repeat = repeat + 1
        if repeat > repeat_len:
          base = base + Z_base[i][-1]
          repeat = 0
      else:
        continue
      '''
    elif i==T-1:
      base = base + Z_base[i][start:]
    else:
      repeat = 0
      base = base + Z_base[i][start]
  return base #string
def base_only_assembly(bases,kmer,start=0):
  # take input array of bases or its idx with no duraing information and consecutive them together
  if type(bases[0]) != str:
    bases = base2num(bases,kmer,op=True)
  sequence = bases[0]
  for i in range(1,len(bases)):
    sequence += bases[i][-1]
  return sequence
################################################################################################
