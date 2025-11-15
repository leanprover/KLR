
def scalar(x): pass

class tensor:
  def __init__(self, dtype, shape):
    self.dtype = dtype
    self.shape = shape

class mutable(tensor):
  pass
