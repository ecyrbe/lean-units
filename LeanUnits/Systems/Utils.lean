import Batteries.Data.Rat.Basic
import Batteries.Classes.RatCast
import Batteries.Data.Rat.Float

namespace Units

instance : Inv Float where
  inv v := 1.0 / v

instance : Pow Float Nat where
  pow v n := v ^ (Float.ofNat n)

instance : Pow Float Int where
  pow v n := v ^ (Float.ofInt n)

instance : Pow Float Rat where
  pow v n := v.pow (Float.ofInt n.num / Float.ofNat n.den)

instance : RatCast Float where
  ratCast q := q.toFloat

end Units
