import Batteries.Data.Rat

namespace Units

def formatExp (e : String) (n : Rat) : String :=
  match n with
  | 1   => e
  | 2   => s!"{e}²"
  | 3   => s!"{e}³"
  | 4   => s!"{e}⁴"
  | 5   => s!"{e}⁵"
  | 6   => s!"{e}⁶"
  | 7   => s!"{e}⁷"
  | 8   => s!"{e}⁸"
  | 9   => s!"{e}⁹"
  | -1  => s!"{e}⁻¹"
  | -2  => s!"{e}⁻²"
  | -3  => s!"{e}⁻³"
  | -4  => s!"{e}⁻⁴"
  | -5  => s!"{e}⁻⁵"
  | -6  => s!"{e}⁻⁶"
  | -7  => s!"{e}⁻⁷"
  | -8  => s!"{e}⁻⁸"
  | -9  => s!"{e}⁻⁹"
  | n   => s!"{e}^{n}"

end Units
