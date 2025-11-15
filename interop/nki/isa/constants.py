from enum import Enum
class reduce_cmd(Enum):
  """Engine Register Reduce commands"""
  idle = 0
  reset = 1
  reset_reduce = 3
  reduce = 2


