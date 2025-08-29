# KLR implemetations of NKI langauge APIs

def par_dim(x): return x

float32 = "float32"

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
