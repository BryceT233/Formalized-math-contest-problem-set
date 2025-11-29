/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem269 (x y z : ℝ) (xne0 : x ≠ 0) (yne0 : y ≠ 0) (zne0 : z ≠ 0)
    (h1 : 9 * x * (15 * z) = (12 * y) ^ 2 )
    (h2 : 1 / x + 1 / z = 2 / y) :
    x / z + z / x = 34 / 15 := by grind
