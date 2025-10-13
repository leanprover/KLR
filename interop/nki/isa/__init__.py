from enum import Enum
# KLR implemetations of NKI ISA APIs

class reduce_cmd(Enum):
  """Engine Register Reduce commands"""
  idle = 0
  reset = 1
  reset_reduce = 3
  reduce = 2

class dge_mode(Enum):
  none = 0
  swde = 1
  hwge = 2
  unknown = 3

def psum_raw_ptr(address, size):
  p_start, f_start = address
  p_size, f_size = size
  p_end = p_start + p_size
  f_end = f_start + f_size
  return psum[p_start:p_end, f_start:f_end]

def sbuf_raw_ptr(address, size):
  p_start, f_start = address
  p_size, f_size = size
  p_end = p_start + p_size
  f_end = f_start + f_size
  return sbuf[p_start:p_end, f_start:f_end]

class reduce_cmd(Enum):
  """Engine Register Reduce commands """
  idle = 0
  reset = 1
  reset_reduce = 2
  reduce = 3
  load_reduce = 4

def psum_raw_ptr(address, size):
  p_start, f_start = address
  p_size, f_size = size
  p_end = p_start + p_size
  f_end = f_start + f_size
  return psum[p_start:p_end, f_start:f_end]

def sbuf_raw_ptr(address, size):
  p_start, f_start = address
  p_size, f_size = size
  p_end = p_start + p_size
  f_end = f_start + f_size
  return sbuf[p_start:p_end, f_start:f_end]
