# KLR implemetations of NKI ISA APIs

def psum_raw_ptr(address, size):
  return psum[address[0]:size[0], address[1]:size[1]]

def sbuf_raw_ptr(address, size):
  return sbuf[address[0]:size[0], address[1]:size[1]]
