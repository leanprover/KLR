# KLR implemetations of NKI langauge APIs

class NKIObject:
    pass

def copy(): pass
def exp(): pass
def add(): pass
def multiply(): pass

def par_dim(x): return x

int32 = "int32"
float16 = "float16"
uint8 = "uint8"

class int8(NKIObject):
  itemsize = 1
  
  def __init__(self, x):
    self.value = x
  
  def __str__(self):
    return "uint8"

class float32(NKIObject):
  itemsize = 4

class tile_size:
  pmax = 128
  psum_fmax = 128

