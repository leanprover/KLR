import frontend
import foo

print("NKI frontend version", frontend.version())

g = 5
def kernel(x,y): return foo.foo(x,a=x+g)

K = frontend.Kernel(kernel)
print("K is", K)
K.specialize()
K.specialize(1, a=2)

ba = K.serialize()
print(ba)
frontend.deserialize(ba)

#def bad1(): raise Exception()
#K = frontend.Kernel(bad1)
