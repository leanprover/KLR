# KLR implemetations of NKI ISA APIs

from enum import Enum
class reduce_cmd(Enum):
  """Engine Register Reduce commands"""
  idle = 0
  reset = 1
  reset_reduce = 3
  reduce = 2

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
