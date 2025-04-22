import frontend

print(frontend.version())

def f(): pass
K = frontend.Kernel(f)
print(K)
K.specialize()
K.specialize(1, a=2)

ba = K.serialize()
print(ba)
frontend.deserialize(ba)
