import Definitions.Def_LatticeAttack_Research_Wall1_TerminalScale506

set_option autoImplicit true

/-! # Part 183 counting prefactor at the physical terminal radius

The exponent in the theta factor is π z²/(1+y²), where z=(52/√3)√(2π/506).
In even dimension the unit-ball formula reduces the numerator J_b to
exp(253) 253! / 253^253. The frequency factor is written with a square root
since its exponent is -253/2.
-/

noncomputable section
namespace SigabaNeo.Wall1.TerminalProjection

private def energy (y : ℝ) : ℝ := Real.pi^2 * 52^2 / (3*253) / (1+y^2)
private def theta (y : ℝ) : ℝ :=
  let e := Real.exp (-energy y)
  1 + 2*e/(1-e^3)

private def prefactor : ℝ :=
  (Real.exp 253 * Nat.factorial 253 / 253^253) /
    (8 * Real.sin 1 ^ 2 * (1 - Real.exp (-(1/2))))

/-- The theta envelope of Part 161. -/
def terminalTheta (u : ℝ) : ℝ :=
  1 + 2 * Real.exp (-Real.pi*u^2) / (1 - Real.exp (-3*Real.pi*u^2))

/-- The one-dimensional lattice Gaussian controlled by each theta factor. -/
theorem integerGaussian_le_terminalTheta {u : ℝ} (hu : 0 < u) :
    (∑' k : ℤ, Real.exp (-Real.pi * u^2 * (k : ℝ)^2)) ≤ terminalTheta u := by
  have hp := theta1_poisson hu 0
  simp only [mul_zero, Real.cos_zero, mul_one] at hp
  have hm := (theta1_mem hu 0).2
  rw [hp] at hm
  refine (le_of_mul_le_mul_left hm hu).trans ?_
  unfold terminalTheta
  apply add_le_add_right
  simpa only [neg_mul, mul_assoc] using tau_le hu

/-- Equation (3) of Part 161, with b=506, T=8, δ=1/2 and 4096 bins. -/
def countingConstantAt (z : ℝ) : ℝ :=
  let J := Real.exp 253 * (2*Real.pi/506)^253 / terminalBallVolume
  J / (8 * Real.sin 1 ^ 2 * (1-Real.exp (-(1/2)))) * ∑ j ∈ Finset.range 4096,
    let x := (j : ℝ)/512
    let y := ((j : ℝ)+1)/512
    (1/512)*(1-x/8)*(1+x^2)^(-(506/4) : ℝ) * terminalTheta (z/Real.sqrt (1+y^2))^506

/-- Use the actual physical radius R=52/√3 in z=R√(2π/b). -/
def terminalCountingConstant : ℝ :=
  countingConstantAt ((52 / Real.sqrt 3) * Real.sqrt (2*Real.pi/506))

private theorem terminal_sum_eq : terminalCountingConstant =
    prefactor * ∑ j ∈ Finset.range 4096, (1/512) * (1 - (j : ℝ)/4096) *
      (theta ((j+1)/512)^506 / Real.sqrt ((1+((j : ℝ)/512)^2)^253)) := by
  have hJ : Real.exp 253 * (2*Real.pi/506)^253 / terminalBallVolume =
      Real.exp 253 * Nat.factorial 253 / 253^253 := by
    rw [terminalBallVolume_eq, show 2*Real.pi/506 = Real.pi/253 by ring, div_pow]
    field_simp [Real.pi_ne_zero]
  have ht (y : ℝ) : terminalTheta
      ((52/Real.sqrt 3)*Real.sqrt (2*Real.pi/506)/Real.sqrt (1+y^2)) = theta y := by
    have he : Real.pi * ((52/Real.sqrt 3)*Real.sqrt (2*Real.pi/506)/Real.sqrt (1+y^2))^2 =
        energy y := by
      simp only [div_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 1+y^2),
        Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi/506), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
      unfold energy
      ring
    unfold terminalTheta theta
    simp only [neg_mul, mul_assoc, he]
    have he3 : Real.exp (-(3*energy y)) = Real.exp (-energy y)^3 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [he3]
  have hr (x : ℝ) : (1+x^2)^(-(506/4) : ℝ) = (Real.sqrt ((1+x^2)^253))⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_natCast (1+x^2) 253,
      ← Real.rpow_mul (by positivity)]
    norm_num
  unfold terminalCountingConstant countingConstantAt
  dsimp only
  rw [hJ]
  apply congrArg (prefactor * ·)
  apply Finset.sum_congr rfl
  intro j _
  rw [ht, hr]
  ring

private theorem sin_one_lower : 0.8414709848078964 ≤ Real.sin 1 := by
  have h := Complex.exp_bound (x := Complex.I) (by simp) (n := 20) (by decide)
  have h' := (Complex.abs_im_le_norm _).trans h
  have him : (Complex.exp Complex.I).im = Real.sin 1 := by
    simpa using (Complex.exp_ofReal_mul_I_im 1)
  rw [Complex.sub_im, him] at h'
  norm_num [Finset.sum_range_succ, Nat.factorial, pow_succ, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.div_im, Complex.normSq_apply] at h'
  linarith [(abs_le.mp h').1]

private theorem prefactor_le : prefactor ≤ 17.8942733769791 := by
  let a : ℚ := 2.718281828459045236
  let b : ℚ := 1.64872127070012814
  have ha := TerminalInterval.exp_upper 1 a (by decide) (by decide) (by decide +kernel)
  have hb := TerminalInterval.exp_lower (1/2) b (by decide +kernel) (by decide +kernel)
  have hJ : Real.exp 253 ≤ (a : ℝ)^253 := by
    have hp := pow_le_pow_left₀ (Real.exp_pos _).le ha 253
    rw [← Real.exp_nat_mul] at hp
    simpa using hp
  have hb' : Real.exp (-(1/2)) ≤ 1 / (b : ℝ) := by
    rw [Real.exp_neg, ← one_div]
    apply one_div_le_one_div_of_le (by norm_num [b])
    simpa using hb
  have hsin := pow_le_pow_left₀ (by norm_num) sin_one_lower 2
  have hd : (8 * (0.8414709848078964 : ℝ)^2 * (1-1/(b : ℝ))) ≤
      8 * Real.sin 1 ^ 2 * (1 - Real.exp (-(1/2))) := by
    apply mul_le_mul (by linarith only [hsin]) (by linarith only [hb'])
      (by norm_num [b]) (by positivity)
  have hdpos : 0 < 8 * Real.sin 1 ^ 2 * (1 - Real.exp (-(1/2))) :=
    lt_of_lt_of_le (by norm_num [b]) hd
  apply (div_le_iff₀ hdpos).2
  calc
    _ ≤ ((a : ℝ)^253 * Nat.factorial 253) / 253^253 := by gcongr
    _ ≤ 17.8942733769791 * (8 * (0.8414709848078964 : ℝ)^2 * (1-1/(b : ℝ))) := by
      have hn := (Rat.cast_le (K := ℝ)).2
        (show a^253 * Nat.factorial 253 / 253^253 ≤
          17.8942733769791 * (8 * (0.8414709848078964 : ℚ)^2 * (1-1/b)) by decide +kernel)
      push_cast at hn
      exact hn
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by norm_num)

/- The theta enclosures use blocks of 32 bins below frequency 1 and blocks
of 256 thereafter. For bin 352 onward one bound per block already suffices
for the entire decaying factor. -/
private def block (j : ℕ) := if j < 512 then j/32 else 16 + (j-512)/256
private def endpoint (k : ℕ) := if k < 16 then 32*(k+1) else 512+256*(k-15)
private def tile (j : ℕ) := if j < 352 then j else 352 + (block j - 11)
private def leftBin (i : ℕ) := if i < 352 then i else
  if i < 357 then 352+32*(i-352) else 512+256*(i-357)

private theorem bin_indices {j : ℕ} (hj : j < 4096) :
    block j < 30 ∧ j+1 ≤ endpoint (block j) ∧ tile j < 371 ∧
    leftBin (tile j) ≤ j ∧ block (leftBin (tile j)) = block j := by
  unfold tile leftBin block endpoint
  split_ifs <;> omega

private def smallArg (k : ℕ) : ℚ := 35.16127839 / (1+((endpoint k : ℚ)/512)^2) / 64

/-- Lower bounds for exp(smallArg) at right endpoints. -/
private def baseBound (i : ℕ) : ℚ :=
  let numerators : Array ℕ := #[
    172850565363316845, 171762538095507462, 170018365500827730, 167711930693145798,
    164957292052464582, 161876149533900150, 158586741063926137, 155195585882061824,
    151792542499614400, 148448890857918057, 145217722058260133, 142135804442956614,
    139226188356865955, 136501000142821379, 133964075333471159, 131613246801331461,
    118417296091197644, 111614300336813529, 107872373686112272, 105647669324416962,
    104233539911363934, 103284522824327124, 102619099168998622, 102135540738906620,
    101773608826072462, 101495929966100249, 101278379692685030, 101104848817530859,
    100964261204629630, 100848805133261203]
  (numerators[i]?.getD 0 : ℚ) / 10^17

/-- Upper bounds for the decaying exponential at right endpoints. -/
private def expBound (i : ℕ) : ℚ :=
  let numerators : Array ℕ := #[
    61527394, 92167810, 177119531, 424528307,
    1225244636, 4095402661, 15237721487, 60774396490,
    251172527116, 1044900040306, 4273112456694, 16864618599318,
    63366578483587, 224546690364624, 746011547569917, 2316463221401690,
    2001847643280194253, 88293790905832083238, 782969672578232101004, 2971427113456296141699,
    7039159670527981392004, 12639915359556597318493, 19115925647481017597525, 25862998679392542461986,
    32460023222594976151596, 38662315449850911347009, 44353545578448553783380, 49498611475840768844147,
    54108937980541440332041, 58219912856897680064264]
  (numerators[i]?.getD 0 : ℚ) / 10^23

/-- Upper bounds for the one-dimensional theta majorant. -/
private def thetaBound (i : ℕ) : ℚ :=
  let numerators : Array ℕ := #[
    1000000000000001231, 1000000000000001844, 1000000000000003543, 1000000000000008491,
    1000000000000024505, 1000000000000081909, 1000000000000304755, 1000000000001215488,
    1000000000005023451, 1000000000020898001, 1000000000085462250, 1000000000337292372,
    1000000001267331570, 1000000004490933808, 1000000014920230952, 1000000046329264429,
    1000040036952865605, 1001765875819332130, 1015659400967966065, 1059430101468735365,
    1140832314135210861, 1253309853058382136, 1385007914526713247, 1526365905181535733,
    1672190456486880492, 1820674263428270940, 1971870432240582646, 2126603513796201988,
    2285887690070576048, 2450673942719434284]
  (numerators[i]?.getD 0 : ℚ) / 10^18

/-- Upward-rounded bounds for the full radial factor, in units of 10⁻¹⁸. -/
private def radialNum (i : ℕ) : ℕ :=
  let numerators : Array ℕ := #[
    1000000000000622887, 999517558129449874, 998071639591250556, 995666458720947467, 992309016487554921, 988009066276564231,
    982779066316094900, 976634119074074735, 969591898042189480, 961672562407126776, 952898660189992547, 943295020510011140,
    932888635698100055, 921708534049064405, 909785644057481580, 897152651031412019, 883843847019523278, 869894975020776982,
    855343068471309023, 840226287020422192, 824583749616679820, 808455365925993199, 791881667096468459, 774903636869831081,
    757562544016762361, 739899777043814472, 721956682083135461, 703774404833505859, 685393737372689251, 666854970607398594,
    648197753068883877, 629460956699889463, 610682550213357217, 591899480533723809, 573147562765520035, 554461379055827358,
    535874186651842641, 517417835378722658, 499122694692892860, 481017590395729288, 463129751024278077, 445484763869798123,
    428106540511886313, 411017291696211976, 394237511327839368, 377785969300094206, 361679712831219358, 345934075937899063,
    330562696636289391, 315577541427600546, 300988936596606940, 286805605827735533, 273034713624574927, 259681914004684062,
    246751403932343749, 234245980947230824, 222167104446711156, 210514960083319857, 199288526746772303, 188485645611251587,
    178103090743450607, 168136640784598585, 158581151240149348, 149430626933622019, 140678294206051250, 132316672468194754,
    124337644743143200, 116732526861596410, 109492135006146158, 102606851328386741, 96066687393848471, 89861345239786747,
    83980275860659749, 78412734965333909, 73147835878460400, 68174599485882148, 63482001150195619, 59059014547563712,
    54894652400436403, 50978004102887395, 47298270255741935, 43844794147498050, 40607090234194874, 37574869686840097,
    34738063088773929, 32086840377434766, 29611628135432436, 27303124344671387, 25152310724553321, 23150462781091077,
    21289157698156332, 19560280205143037, 17956026557142462, 16468906764384259, 15091745207294483, 13817679772150673,
    12640159640103460, 11552941859091147, 10550086825153651, 9625952794210777, 8775189541740334, 7992731281873819,
    7273788952121042, 6613841964096721, 6008629514631906, 5454141545543223, 4946609434164914, 4482496490578551,
    4058488331353764, 3671483193585565, 3318582247119744, 2997079957132062, 2704454543699214, 2438358579694630,
    2196609763280454, 1977181896464401, 1778196096658742, 1597912263926634, 1434720822633246, 1287134752537611,
    1153781920964703, 1033397724582683, 924818046471883, 826972531602575, 738878181528819, 659633267045467,
    588411555733245, 524456849720579, 467077827611373, 415643183317579, 369577053620206, 328354725318912,
    291498612306159, 258574492296046, 229187992580231, 202981313912190, 179630181461969, 158841011720674,
    140348284255967, 123912107316477, 109315966444255, 96364645471053, 84882309537816, 74710740079257,
    65707712049719, 57745504025946, 50709532200979, 44497099675783, 39016252856577, 34184737171892,
    29929044730419, 26183546945426, 22889705551112, 19995355828305, 17454056239464, 15224499044163,
    13269976825031, 11557900199160, 10059362320709, 8748746096090, 7603370333702, 6603171333379,
    5730416694799, 4969448369703, 4306452229689, 3729251639926, 3227122740037, 2790629328291,
    2411475426903, 2082373774897, 1796928651338, 1549531576262, 1335268570081, 1149837775095,
    989476355740, 850895697859, 731224022255, 627955614620, 538905953195, 462172087775,
    396097689371, 339242249576, 290353962817, 248345873712, 212274916123, 181323510493,
    154783422191, 132041616079, 112567871728, 95903949958, 81654124910, 69476916905,
    59077880199, 50203316543, 42634800572, 36184416210, 30690615406, 26014620948,
    22037304534, 18656479595, 15784555753, 13346508280, 11278121720, 9524471909,
    8038615096, 6780456838, 5715776796, 4815388619, 4054416781, 3411674580,
    2869129568, 2411444484, 2025583325, 1700473582, 1426716846, 1196341052,
    1002588530, 839734816, 702933889, 588086067, 491725327, 410923269,
    343207328, 286491158, 239015429, 199297514, 166088762, 138338233,
    115161947, 95816822, 79678600, 66223174, 55010783, 45672669,
    37899796, 31433334, 26056633, 21588457, 17877285, 14796511,
    12240413, 10120757, 8363947, 6908632, 5703699, 4706585,
    3881873, 3200103, 2636786, 2171578, 1787585, 1470787,
    1209555, 994251, 816887, 670848, 550660, 451796,
    370511, 303711, 248842, 203793, 166824, 136501,
    111639, 91266, 74578, 60914, 49732, 40586,
    33107, 26995, 22002, 17925, 14598, 11883,
    9669, 7864, 6394, 5196, 4221, 3428,
    2782, 2258, 1831, 1485, 1203, 975,
    790, 639, 517, 419, 339, 274,
    221, 179, 145, 117, 94, 76,
    61, 50, 40, 32, 26, 21,
    17, 14, 11, 9, 7, 6,
    5, 4, 3, 3, 2, 2,
    2, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1,
    1, 1, 1, 1]
  numerators[i]?.getD 1

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
private theorem block_checks : ∀ k : Fin 30,
    0 ≤ smallArg k ∧ baseBound k ≤ TerminalInterval.taylor (smallArg k) 20 ∧
    0 < baseBound k ∧ 1 ≤ expBound k * (baseBound k)^64 ∧
    0 < expBound k ∧ expBound k < 1 ∧
    1 + 2 * expBound k / (1-(expBound k)^3) ≤ thetaBound k := by decide +kernel

private def radialBound (i : ℕ) : ℚ := (radialNum i : ℚ) / 10^18

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
private theorem radial_checks : ∀ i : Fin 371,
    (thetaBound (block (leftBin i)))^1012 ≤ (radialBound i)^2 *
        (1 + ((leftBin i : ℚ)/512)^2)^253 := by decide +kernel

private theorem theta_enclosed {j : ℕ} (hj : j < 4096) :
    0 ≤ theta (((j : ℝ)+1)/512) ∧
    theta (((j : ℝ)+1)/512) ≤ (thetaBound (block j) : ℝ) := by
  let k : Fin 30 := ⟨block j, (bin_indices hj).1⟩
  obtain ⟨hx, hb, hbpos, hinv, hepos, heone, htheta⟩ := block_checks k
  have hpi : (35.16127839 : ℝ) ≤ Real.pi^2 * 52^2 / (3*253) := by
    have h' := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d20.le 2
    linarith only [h']
  have hy : ((j : ℝ)+1)/512 ≤ (endpoint k : ℝ)/512 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact_mod_cast (bin_indices hj).2.1
  have hxenergy : (64 : ℕ)*(smallArg k : ℝ) ≤ energy (((j : ℝ)+1)/512) := by
    unfold energy smallArg
    push_cast
    calc
      _ = 35.16127839 / (1+((endpoint k : ℝ)/512)^2) := by ring
      _ ≤ _ := div_le_div₀ (by positivity) hpi (by positivity)
        (by gcongr)
  have he := (Real.exp_le_exp.mpr hxenergy)
  rw [Real.exp_nat_mul] at he
  have hp : 0 < (baseBound k : ℝ) := by exact_mod_cast hbpos
  have hpow := (pow_le_pow_left₀ hp.le (TerminalInterval.exp_lower _ _ hx hb) 64).trans he
  have hp' : 0 < (expBound k : ℝ) := by exact_mod_cast hepos
  have hu : (expBound k : ℝ) < 1 := by exact_mod_cast heone
  have h1 : (1:ℝ) ≤ (expBound k : ℝ) * (baseBound k : ℝ)^64 := by exact_mod_cast hinv
  have hdec : Real.exp (-energy (((j : ℝ)+1)/512)) ≤ (expBound k : ℝ) := by
    rw [Real.exp_neg, ← one_div, div_le_iff₀ (Real.exp_pos _)]
    exact h1.trans (mul_le_mul_of_nonneg_left hpow hp'.le)
  have he3 : (expBound k : ℝ)^3 < 1 := by simpa using pow_lt_pow_left₀ hu hp'.le (by decide : 3 ≠ 0)
  have he3' := pow_le_pow_left₀ (Real.exp_pos _).le hdec 3
  unfold theta
  dsimp only
  constructor
  · have hden := sub_pos.mpr (he3'.trans_lt he3)
    positivity
  · calc
      _ ≤ 1 + 2*(expBound k : ℝ)/(1-(expBound k : ℝ)^3) := by
        apply add_le_add_right
        apply div_le_div₀ (by positivity) (by gcongr) (sub_pos.mpr he3) (by linarith only [he3'])
      _ ≤ _ := by
        have hh := (Rat.cast_le (K := ℝ)).2 htheta
        push_cast at hh
        exact hh

private theorem radial_enclosed {j : ℕ} (hj : j < 4096) :
    theta (((j : ℝ)+1)/512)^506 / Real.sqrt ((1+((j : ℝ)/512)^2)^253) ≤
      (radialBound (tile j) : ℝ) := by
  obtain ⟨_, _, hi, hl, hk⟩ := bin_indices hj
  have h := radial_checks ⟨tile j, hi⟩
  change (thetaBound (block (leftBin (tile j))))^1012 ≤ _ at h
  rw [hk] at h
  have hr : (thetaBound (block j) : ℝ)^1012 ≤ (radialBound (tile j) : ℝ)^2 *
      (1+((leftBin (tile j) : ℝ)/512)^2)^253 := by
    have hh := (Rat.cast_le (K := ℝ)).2 h
    push_cast at hh
    exact hh
  have hw : 0 ≤ (radialBound (tile j) : ℝ) := by unfold radialBound; push_cast; positivity
  have hx : (leftBin (tile j) : ℝ) ≤ j := by exact_mod_cast hl
  have hr' : (thetaBound (block j) : ℝ)^1012 ≤ (radialBound (tile j) : ℝ)^2 *
      (1+((j : ℝ)/512)^2)^253 := hr.trans (by gcongr)
  obtain ⟨h0, htheta⟩ := theta_enclosed hj
  apply (div_le_iff₀ (by positivity)).2
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul]
  exact (pow_le_pow_left₀ h0 htheta 1012).trans hr'

private def weightedSum : ℕ := ∑ j ∈ Finset.range 4096, (4096-j) * radialNum (tile j)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem weighted_check :
    178942733769791 * weightedSum ≤ 1422743743939 * 10 * (512*4096*10^18) := by
  decide +kernel

/-- Kernel-checked upper enclosure for the full 4096-bin majorant at R=52/√3. -/
theorem terminalCountingConstant_le : terminalCountingConstant ≤ 1.422743743939 := by
  have hsum := Finset.sum_le_sum (s := Finset.range 4096) (fun (j : ℕ) hj ↦
    mul_le_mul_of_nonneg_left (radial_enclosed (Finset.mem_range.mp hj))
      (show 0 ≤ (1/512 : ℝ)*(1-(j : ℝ)/4096) by
        have h : (j : ℝ) ≤ 4096 := by exact_mod_cast (Finset.mem_range.mp hj).le
        nlinarith))
  have heq : (∑ j ∈ Finset.range 4096, (1/512 : ℝ)*(1-(j : ℝ)/4096)*
      (radialBound (tile j) : ℝ)) = (weightedSum : ℝ) / (512*4096*10^18) := by
    unfold weightedSum
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.cast_sub (Finset.mem_range.mp hj).le]
    unfold radialBound
    push_cast
    ring
  rw [heq] at hsum
  have hpre : 0 ≤ prefactor := by
    have he : Real.exp (-(1/2)) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    unfold prefactor
    positivity
  rw [terminal_sum_eq]
  calc
    _ ≤ prefactor * ((weightedSum : ℝ) / (512*4096*10^18)) := mul_le_mul_of_nonneg_left hsum hpre
    _ ≤ 17.8942733769791 * ((weightedSum : ℝ) / (512*4096*10^18)) :=
      mul_le_mul_of_nonneg_right prefactor_le (by positivity)
    _ ≤ _ := by
      have h : (178942733769791 : ℝ) * weightedSum ≤ 1422743743939 * 10 *
          (512*4096*10^18) := by exact_mod_cast weighted_check
      linarith

/-- The unconditional numerical value of the first-moment majorant, before
relating it to the candidate count of a particular history. -/
theorem terminal_majorant_lt :
    terminalCountingConstant * ((52 / Real.sqrt 3) /
      terminalScale (Real.exp (terminalLogFloor 406)))^506 < 3.209079 / 10^14 := by
  let g := terminalScale (Real.exp (terminalLogFloor 406))
  have hg : 31.9457118986 ≤ g := terminalScale_406.le
  have hg0 : 0 < g := by linarith
  have hr : ((52 / Real.sqrt 3)/g)^2 ≤ (52^2/3)/(31.9457118986 : ℝ)^2 := by
    rw [div_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    exact pow_le_pow_left₀ (by norm_num) hg 2
  change terminalCountingConstant * ((52 / Real.sqrt 3)/g)^506 < _
  rw [show (506 : ℕ) = 2*253 by decide, pow_mul]
  apply lt_of_le_of_lt (mul_le_mul terminalCountingConstant_le
    (pow_le_pow_left₀ (sq_nonneg _) hr 253) (by positivity) (by norm_num))
  have hn := (Rat.cast_lt (K := ℝ)).2 (show (1.422743743939 : ℚ) *
    ((52^2/3)/31.9457118986^2)^253 < 3.209079/10^14 by decide +kernel)
  push_cast at hn
  exact hn

open WithLp DecoupledDecoder

/-- The terminal discrepancy with both scalar enclosures discharged. The remaining
hypothesis is the Part 161 candidate-count inequality at the deterministic scale floor. -/
theorem discrepancy_506_of_terminal_count
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (M K : Submodule ℤ V) [DiscreteTopology K] [IsZLattice ℝ K] [Fintype (Marks M K)]
    (u : Marks M K → V) (htors : ∀ a ∈ K, 3329 • a ∈ M) (hMK : M ≤ K)
    (huK : ∀ g, u g ∈ K) (hu : ∀ g, M.mkQ (u g) = g.val) {x : V}
    (hx : IsShortest M x) (v : Marks M K → WindowSpace V)
    (hv : ∀ g, IsShortest (appendWindow M (u g)) (v g)) (htie : ∀ g, HorizontalAgreement x (v g))
    (hwidth : Module.finrank ℝ V + 1 = 506)
    (hcount : (candidates K (52 / Real.sqrt 3)).card / (Fintype.card (Marks M K) : ℝ) ≤
      terminalCountingConstant * ((52 / Real.sqrt 3) /
        terminalScale (Real.exp (terminalLogFloor 406)))^506) :
    mass (fun b ↦ ¬ (ShortProjection (appendWindow M (u b)) (v b) 26 ↔ ShortProjection M x 26))
      < 3.210 / 10^14 :=
  discrepancy_506 M K u htors hMK huK hu hx v hv htie hwidth terminalCountingConstant_le
    terminalScale_406.le (by simpa only [hwidth] using hcount)

end SigabaNeo.Wall1.TerminalProjection

#print axioms SigabaNeo.Wall1.TerminalProjection.integerGaussian_le_terminalTheta
#print axioms SigabaNeo.Wall1.TerminalProjection.terminalCountingConstant_le
#print axioms SigabaNeo.Wall1.TerminalProjection.terminal_majorant_lt
#print axioms SigabaNeo.Wall1.TerminalProjection.discrepancy_506_of_terminal_count
