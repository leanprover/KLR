import pytest

import nki.isa as nisa 
import nki.language as nl 

from runner import *

def test_dynamic_ap():
    t = nl.ndarray((128, 128, 128), nl.float32, name="t")
    ap1 = t.ap([[128*128, 128], [128, 1], [1, 1]])
    ap2 = t.ap([[128*128, 128], [128, 1], [1, 1]], offset=32)
    i = 1 # no way to produce a dynamic scalar yet, but it int is also immediate 
    ap2 = t.ap([[128*128, 128], [128, 1], [1, 1]], offset=32, scalar_offset=i)
    v = nl.ndarray((128,1), nl.float32, name="v")
    ap3 = t.ap([[128*128, 128], [128, 1], [1, 1]], offset=32, vector_offset=v, indirect_dim=0)

def test_dyn_ap_fail():
    t = nl.ndarray((128, 128, 128), nl.float32, name="t")
    i = 1 # no way to produce a dynamic scalar yet, but it int is also immediate 
    ap2 = t.ap(
        [[128*128, 128], [128, 1], [1, 1]], offset=32, scalar_offset=i
    ).ap(
        [[128*128, 128], [128, 1], [1, 1]], offset=32, scalar_offset=i
    )

@pytest.mark.parametrize("f", [
  test_dynamic_ap
  ])
def test_succeed(f):
    F = Kernel(f)
    F.specialize()
    rv = F.trace("out.klr")
    rv = json.loads(rv)
    errs = rv["errors"]
    assert errs is None or errs == [], f"errors are set. errors {errs}"

    if os.path.exists("out.klr"):
        os.remove("out.klr")

@pytest.mark.parametrize("f", [
  test_dyn_ap_fail
  ])
def test_fail(f):
    F = Kernel(f)
    F.specialize()
    rv = F.trace("out.klr")
    rv = json.loads(rv)
    errs = rv["errors"]
    assert errs and len(errs) > 0

    if os.path.exists("out.klr"):
        os.remove("out.klr")

if __name__ == "__main__":
    test_succeed(test_dynamic_ap)
    test_fail(test_dyn_ap_fail)
