# KLR implemetations of NKI langauge APIs

def ndarray(shape, dtype, buffer=None, name=''):
  buffer = buffer or sbuf
  return buffer.view(dtype, shape)
