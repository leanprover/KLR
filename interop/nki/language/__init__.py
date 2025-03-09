# KLR implemetations of NKI langauge APIs

def ndarray(shape, dtype, buffer=None, name=''):
  if buffer == None:
    buffer = sbuf
  else:
    assert buffer.size[0] == shape[0]
  return buffer.view(dtype, shape, name)
