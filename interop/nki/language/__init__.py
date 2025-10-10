# KLR implemetations of NKI langauge APIs

class NKIObject:
    pass

def par_dim(x): return x

float16 = "float16"

class uint8(NKIObject):
  itemsize = 1

class float32(NKIObject):
  itemsize = 4

class tile_size:
  pmax = 128
  psum_fmax = 128

def ndarray(shape, dtype, buffer=None, name=''):
  if buffer == None:
    buffer = sbuf
  elif buffer == nki.language.sbuf:
    buffer = sbuf
  elif buffer == nki.language.psum:
    buffer = psum
  else:
    assert False, "invalid buffer argument"
  return buffer.view(dtype, shape, name)

