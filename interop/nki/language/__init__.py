# KLR implemetations of NKI langauge APIs

class NKIObject:
    pass

def par_dim(x): return x

bfloat16 = "bfloat16"
float32 = "float32"
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

