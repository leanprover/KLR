# KLR implementations of NKI ISA APIs

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
