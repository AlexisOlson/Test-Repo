import Lake
open Lake DSL

package stoch_to_det_lower_bound

require stoch_to_det from git
  "https://github.com/DLorell/stoch_to_det.git" @ "main"

@[default_target]
lean_lib LowerBound190
