import Lake
open Lake DSL

package stoch_to_det_lower_bound

require stoch_to_det from git
  "https://github.com/DLorell/stoch_to_det.git" @
    "299c75264b07db05eab8e6d232ef88e0988f4790"

@[default_target]
lean_lib LowerBound190
