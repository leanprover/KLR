import os
import json
from klr.frontend import Kernel

def run_success(f, args):
  F = Kernel(f)   # parse python
  j = json.loads(F.specialize(args))
  if len(j['errors']) > 0:
    assert False, j['errors'][0]
  j = json.loads(F.trace("tmp.klr"))
  if len(j['errors']) > 0:
    assert False, j['errors'][0]
  os.remove("tmp.klr")

def run_fail(f, args):
  F = Kernel(f)   # parse python
  j = json.loads(F.specialize(args))
  if len(j['errors']) > 0:
    return
  j = json.loads(F.trace("tmp.klr"))
  if len(j['errors']) > 0:
    return
  os.remove("tmp.klr")
  assert False, "expecting failure"
