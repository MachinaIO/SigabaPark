import Definitions.Def_LatticeAttack_Research_Wall1_ControlledFlagEnvelope
import Definitions.Def_LatticeAttack_Research_Wall1_ControlledPlaneCharges

set_option autoImplicit true

/-! Outward rational bounds for the complete triangular Part 192 sum.
Each nontrivial entry is measured in units of 10⁻²⁶. Entries omitted from a
row are bounded by one such unit. The kernel checks every rounding inequality. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane.FlagEnvelope
open Real Finset TerminalProjection TerminalInterval

set_option maxRecDepth 10000
set_option maxHeartbeats 0

-- Cumulative log caps, lower determinant logs, and lower log width corrections.
private def logs : Array (ℕ × ℕ × ℕ) := #[
  (0, 3244170895030000, 2194329801438),
  (0, 3236060467792424, 2193340681432),
  (143841036232, 3227950040554848, 2192349600830),
  (389048349492, 3219839613317272, 2191356551844),
  (749780192847, 3211729186079696, 2190361526640),
  (1197155433772, 3203618758842120, 2189364517336),
  (1742613600000, 3195508331604544, 2188365516005),
  (2379622790284, 3187397904366968, 2187364514670),
  (3115653006363, 3179287477129392, 2186361505306),
  (3958914617920, 3171177049891816, 2185356479842),
  (4878942651645, 3163066622654240, 2184349430156),
  (5871902852581, 3154956195416664, 2183340348078),
  (6934409032759, 3146845768179088, 2182329225388),
  (8063441424904, 3138735340941512, 2181316053815),
  (9256284916496, 3130624913703936, 2180300825040),
  (10510481205617, 3122514486466360, 2179283530691),
  (11823791008514, 3114404059228784, 2178264162346),
  (13194163710579, 3106293631991208, 2177242711531),
  (14619712648000, 3098183204753632, 2176219169720),
  (16098694727135, 3090072777516056, 2175193528335),
  (17629493438727, 3081962350278480, 2174165778744),
  (19210604565990, 3073856930897123, 2173135912263),
  (20840624056638, 3065767530131144, 2172103920152),
  (22518237652193, 3057694116323200, 2171069793620),
  (24220575477663, 3049636657878513, 2170033523819),
  (25988848706973, 3041595123264745, 2168995101847),
  (27801228495819, 3033569481011873, 2167954518745),
  (29656681436809, 3025559699712070, 2166911765499),
  (31554229397803, 3017565748019579, 2165866833040),
  (33492944922317, 3009587594650591, 2164819712238),
  (35471947144707, 3001625208383123, 2163770393910),
  (37490398148339, 2993678558056895, 2162718868811),
  (39547499706860, 2985747612573209, 2161665127641),
  (41642490358322, 2977832340894827, 2160609161040),
  (43774642769739, 2969932712045848, 2159550959587),
  (45943261356106, 2962048695111591, 2158490513802),
  (48147680123206, 2954180259238469, 2157427814146),
  (50387260707937, 2946327373633871, 2156362851017),
  (52661390593576, 2938490007566041, 2155295614753),
  (54969481480460, 2930668130363957, 2154226095628),
  (57310967795169, 2922861711417213, 2153154283857),
  (59685305323496, 2915070720175898, 2152080169588),
  (62091969954345, 2907295126150475, 2151003742907),
  (64530456523303, 2899534898911663, 2149924993837),
  (67000277745985, 2891790008090319, 2148843912335),
  (69500963232435, 2884060423377318, 2147760488292),
  (72032058574871, 2876346114523433, 2146674711535),
  (74593124501937, 2868647051339220, 2145586571824),
  (77183736093400, 2860963203694897, 2144496058851),
  (79803482049869, 2853294541520227, 2143403162241),
  (82451964012716, 2845641034804400, 2142307871551),
  (85128795929868, 2838002653595916, 2141210176269),
  (87833603463598, 2830379368002469, 2140110065815),
  (90566023436827, 2822771148190827, 2139007529535),
  (93325703314791, 2815177964386718, 2137902556710),
  (96112300719256, 2807599786874712, 2136795136545),
  (98925482972698, 2800036585998105, 2135685258176),
  (101764926670146, 2792488332158804, 2134572910665),
  (104630317276577, 2784954995817209, 2133458083001),
  (107521348747946, 2777436547492099, 2132340764101),
  (110437723174110, 2769932957760517, 2131220942804),
  (113379150442069, 2762444197257654, 2130098607877),
  (116345347918059, 2754970236676733, 2128973748010),
  (119336040147181, 2747511046768897, 2127846351816),
  (122350958569351, 2740066598343092, 2126716407833),
  (125389841250451, 2732636862265955, 2125583904517),
  (128452432627671, 2725221809461698, 2124448830250),
  (131538483268088, 2717821410911994, 2123311173331),
  (134647749639629, 2710435637655867, 2122170921982),
  (137779993893611, 2703064460789574, 2121028064342),
  (140934983658133, 2695707851466495, 2119882588468),
  (144112491841628, 2688365780897019, 2118734482338),
  (147312296445958, 2681038220348431, 2117583733844),
  (150534180388461, 2673725141144801, 2116430330795),
  (153777931332416, 2666426514666870, 2115274260916),
  (157043341525425, 2659142312351939, 2114115511846),
  (160330207645246, 2651872505693757, 2112954071138),
  (163638330652643, 2644617066242409, 2111789926258),
  (166967515650859, 2637375965604206, 2110623064585),
  (170317571751329, 2630149175441573, 2109453473408),
  (173688311945289, 2622936667472937, 2108281139929),
  (177079552980954, 2615738413472618, 2107106051256),
  (180491115245961, 2608554385270719, 2105928194410),
  (183922822654797, 2601384554753013, 2104747556317),
  (187374502540940, 2594228893860836, 2103564123812),
  (190845985553468, 2587087374590976, 2102377883635),
  (194337105557906, 2579959968995562, 2101188822433),
  (197847699541084, 2572846649181957, 2099996926755),
  (201377607519813, 2565747387312648, 2098802183056),
  (204926672453176, 2558662155605136, 2097604577693),
  (208494740158264, 2551590926331829, 2096404096924),
  (212081659229174, 2544533671819931, 2095200726909),
  (215687280959123, 2537490364451338, 2093994453706),
  (219311459265521, 2530460976662524, 2092785263274),
  (222954050617859, 2523445480944439, 2091573141469),
  (226614913968285, 2516443849842398, 2090358074042),
  (230293910684739, 2509456055955974, 2089140046643),
  (233990904486524, 2502482071938890, 2087919044815),
  (237705761382211, 2495521870498915, 2086695053996),
  (241438349609762, 2488575424397754, 2085468059515),
  (245188539578777, 2481642706450944, 2084238046595),
  (248956203814768, 2474723689527744, 2083005000347),
  (252741216905371, 2467818346551032, 2081768905774),
  (256543455448412, 2460926650497199, 2080529747767),
  (260362798001741, 2454048574396042, 2079287511103),
  (264199125034772, 2447184091330658, 2078042180447),
  (268052318881635, 2440333174437340, 2076793740348),
  (271922263695895, 2433495796905471, 2075542175239),
  (275808845406753, 2426671931977420, 2074287469436),
  (279711951676681, 2419861552948436, 2073029607137),
  (283631471860426, 2413064633166545, 2071768572421),
  (287567296965325, 2406281146032444, 2070504349244),
  (291519319612887, 2399511064999399, 2069236921443),
  (295487434001583, 2392754363573139, 2067966272728),
  (299471535870796, 2386011015311753, 2066692386689),
  (303471522465892, 2379280993825587, 2065415246787),
  (307487292504362, 2372564272777141, 2064134836356),
  (311518746142999, 2365860825880964, 2062851138603),
  (315565784946061, 2359170626903554, 2061564136605),
  (319628311854395, 2352493649663254, 2060273813309),
  (323706231155477, 2345829868030148, 2058980151526),
  (327799448454332, 2339179255925961, 2057683133938),
  (331907870645312, 2332541787323956, 2056382743088),
  (336031405884689, 2325917436248833, 2055078961384),
  (340169963564040, 2319306176776625, 2053771771097),
  (344323454284390, 2312707983034599, 2052461154357),
  (348491789831094, 2306122829201154, 2051147093154),
  (352674883149421, 2299550689505720, 2049829569335),
  (356872648320821, 2292991538228657, 2048508564604),
  (361085000539856, 2286445349701153, 2047184060518),
  (365311856091756, 2279912098305126, 2045856038489),
  (369553132330600, 2273391758473123, 2044524479779),
  (373808747658082, 2266884304688219, 2043189365501),
  (378078621502846, 2260389711483918, 2041850676616),
  (382362674300383, 2253907953444052, 2040508393930),
  (386660827473453, 2247439005202684, 2039162498098),
  (390973003413027, 2240982841444006, 2037812969613),
  (395299125459729, 2234539436902243, 2036459788814),
  (399639117885756, 2228108766361550, 2035102935878),
  (403992905877270, 2221690804655918, 2033742390821),
  (408360415517235, 2215285526669072, 2032378133495),
  (412741573768698, 2208892907334374, 2031010143585),
  (417136308458489, 2202512921634724, 2029638400612),
  (421544548261326, 2196145544602465, 2028262883926),
  (425966222684327, 2189790751319282, 2026883572707),
  (430401262051895, 2183448516916105, 2025500445960),
  (434849597490983, 2177118816573013, 2024113482519),
  (439311160916713, 2170801625519137, 2022722661038),
  (443785885018352, 2164496919032561, 2021327959994),
  (448273703245617, 2158204672440227, 2019929357684),
  (452774549795315, 2151924861117839, 2018526832220),
  (457288359598300, 2145657460489764, 2017120361532),
  (461815068306739, 2139402446028938, 2015709923361),
  (466354612281677, 2133159793256769, 2014295495260),
  (470906928580888, 2126929477743044, 2012877054593),
  (475471954947019, 2120711475105828, 2011454578527)]

private def nontrivial : Array (Array ℕ) := #[
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[3],
  #[6],
  #[20],
  #[74],
  #[281, 4],
  #[1042, 12],
  #[3731, 37],
  #[12899, 119, 3],
  #[43003, 379, 5],
  #[138175, 1170, 11],
  #[427683, 3484, 29],
  #[1274609, 9990, 78],
  #[3655877, 27563, 204, 3],
  #[10086957, 73125, 518, 5],
  #[26625582, 185508, 1260, 10],
  #[66468165, 444863, 2899, 20],
  #[156855840, 1007956, 6301, 40],
  #[349745852, 2156736, 12931, 77],
  #[736473880, 4355879, 25036, 141],
  #[1463856386, 8299590, 45706, 246, 3],
  #[2745078054, 14911228, 78635, 404, 3],
  #[4854002134, 25247310, 127426, 625, 4],
  #[8089156609, 40264810, 194384, 911, 6],
  #[12697798180, 60451030, 278977, 1249, 7],
  #[18764376167, 85389121, 376473, 1609, 8],
  #[26089972480, 113414846, 477417, 1947, 9],
  #[34111010946, 141562371, 568586, 2211, 10],
  #[41912062258, 165948166, 635564, 2355, 10],
  #[48366321206, 182588700, 666363, 2351, 10],
  #[52388592712, 188441271, 654889, 2199, 9],
  #[53228459603, 182304044, 602896, 1926, 7],
  #[50696966529, 165213518, 519562, 1577, 6],
  #[45233664282, 140161227, 418843, 1208, 5],
  #[37782203849, 111234693, 315626, 864, 4],
  #[29522661021, 82522516, 222170, 577, 3],
  #[21565331940, 57188250, 145970, 360],
  #[14715380621, 36992860, 89448, 209],
  #[9372946253, 22318882, 51083, 114],
  #[5568479802, 12549570, 27166, 58],
  #[3083269480, 6571086, 13442, 28],
  #[1589829613, 3201390, 6184, 13],
  #[762772708, 1449992, 2643, 6],
  #[340233712, 610016, 1049, 3],
  #[140967828, 238166, 386],
  #[54204622, 86215, 133],
  #[19325445, 28911, 43],
  #[6382524, 8972, 14],
  #[1950777, 2575, 5],
  #[551247, 683],
  #[143870, 168],
  #[34645, 39],
  #[7690, 9],
  #[1572, 3],
  #[297],
  #[52],
  #[10],
  #[3],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[],
  #[]]

private def cum (k : ℕ) : ℚ := (logs[k]!.1:ℚ)/10^12
private def floorLog (k : ℕ) : ℚ := (logs[k]!.2.1:ℚ)/10^12
private def widthLog (j : ℕ) : ℚ := (logs[j]!.2.2:ℚ)/10^12
private def units (i j : ℕ) : ℕ := ((nontrivial[i]!)[j]?).getD 1

private def up (x : ℚ) := taylor x 20 + x^20*21/(Nat.factorial 20 * 20)
private theorem exp_up {x : ℚ} {n : ℕ} (hn : 0 < n) (hx : 0 ≤ x/n) (hx' : x/n ≤ 1) :
    exp (x:ℝ) ≤ ((up (x/n)^n : ℚ):ℝ) := by
  have e : (x:ℝ) = (n:ℝ)*((x/n:ℚ):ℝ) := by push_cast; field_simp
  rw [e,exp_nat_mul,Rat.cast_pow]
  exact pow_le_pow_left₀ (exp_pos _).le (exp_upper _ _ hx hx' le_rfl) _

private theorem exp_down {x : ℚ} {n : ℕ} (hn : 0 < n) (hx : 0 ≤ x/n) :
    ((taylor (x/n) 20^n:ℚ):ℝ) ≤ exp (x:ℝ) := by
  have e : (x:ℝ) = (n:ℝ)*((x/n:ℚ):ℝ) := by push_cast; field_simp
  have h := exp_lower (x/n) _ hx le_rfl
  rw [e,exp_nat_mul,Rat.cast_pow]
  exact pow_le_pow_left₀ (by exact_mod_cast (show 0 ≤ taylor (x/n) 20 by
    unfold taylor; positivity)) h _

private theorem log_lower {a b : ℚ} (hb : 0 < b) (hx : 0 ≤ a/16) (hx' : a/16 ≤ 1)
    (h : up (a/16)^16 ≤ b) : (a:ℝ) ≤ log (b:ℝ) := by
  apply (le_log_iff_exp_le (by exact_mod_cast hb)).mpr
  exact (exp_up (n := 16) (by decide +kernel) (by simpa using hx) (by simpa using hx')).trans
    ((Rat.cast_le (K := ℝ)).2 h)

private theorem log_upper {a b : ℚ} (ha : 0 < a) (hb : 0 ≤ b/16)
    (h : a ≤ taylor (b/16) 20 ^ 16) : log (a:ℝ) ≤ b := by
  apply (log_le_iff_le_exp (by exact_mod_cast ha)).mpr
  exact ((Rat.cast_le (K := ℝ)).2 h).trans (exp_down (n := 16) (by decide +kernel) (by simpa using hb))

private theorem floor_le (i : ℕ) (hi : i ≤ 154) : (floorLog i:ℝ) ≤ terminalLogFloor i := by
  have low : (8.110427237575:ℝ) ≤ log 3329 := by
    simpa using (log_lower (a:=8.110427237575) (b:=3329) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel))
  have high : log 3329 ≤ 8.110427237576 := by
    simpa using (log_upper (a:=3329) (b:=8.110427237576) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  have cap : log 56.2142 ≤ 4.029169394024 := by
    simpa using (log_upper (a:=56.2142) (b:=4.029169394024) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  induction i with
  | zero =>
    rw [terminalLogFloor,log_pow]
    have hh : floorLog 0 = 400*8.110427237575 := by decide +kernel
    rw [hh]; push_cast; linarith
  | succ i ih =>
    have cert : ∀ i : Fin 154, floorLog (i.val+1) ≤ max (floorLog i-8.110427237576)
      (505/506*floorLog i-4.029169394024/2) := by decide +kernel
    have hh := (Rat.cast_le (K := ℝ)).2 (cert ⟨i,by omega⟩)
    push_cast at hh
    apply hh.trans
    rw [terminalLogFloor]
    have ih' := ih (by omega)
    apply max_le_max <;> linarith

private theorem caps_diff (a b : ℕ) (hab : a ≤ b) (hb : b ≤ 155) :
    logCaps b-logCaps a ≤ (cum b:ℝ)-cum a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b _ ih =>
    have cert : ∀ i : Fin 155, cum (i.val+1) = cum i + logCap (i.val+1) := by decide +kernel
    have eq := congrArg (fun x : ℚ ↦ (x:ℝ)) (cert ⟨b,by omega⟩)
    change (cum (b+1):ℝ) = ((cum b+logCap (b+1):ℚ):ℝ) at eq
    rw [Rat.cast_add] at eq
    have hs : logCaps (b+1) = logCaps b + log (flagCap (b+1)) := sum_Icc_succ_top (by omega) _
    rw [eq,hs]
    linarith [log_flagCap (b+1) hb, ih (by omega)]

private theorem width_le (j : ℕ) (hj : j < 155) :
    log (sqrt (2*π/(506-j:ℝ))) ≤ -(widthLog j:ℝ) := by
  have cert : ∀ j : Fin 155, 0 ≤ 2*widthLog j/8 ∧ 2*widthLog j/8 ≤ 1 ∧
      (up (2*widthLog j/8)^8)*(2*3.14159265358979323847) ≤ 506-(j.val:ℚ) := by decide +kernel
  obtain ⟨hn,hh,H⟩ := cert ⟨j,hj⟩
  have ht := exp_up (x:=2*widthLog j) (n:=8) (by decide +kernel) (by simpa using hn) (by simpa using hh)
  push_cast at ht
  have H' := (Rat.cast_le (K := ℝ)).2 H
  push_cast at H'
  have hj' : (j:ℝ) < 155 := by exact_mod_cast hj
  have hp : 0 < 506-(j:ℝ) := by linarith
  have e : exp (2*(widthLog j:ℝ)) * (2*π) ≤ 506-(j:ℝ) := by
    apply le_trans _ H'
    apply mul_le_mul ht _ (by positivity) ((exp_pos _).le.trans ht)
    linarith [pi_lt_d20]
  rw [log_sqrt (by positivity), log_div (by positivity) hp.ne']
  have h := log_le_log (mul_pos (exp_pos _) (by positivity)) e
  rw [log_mul (exp_pos _).ne' (by positivity),log_exp] at h
  linarith

private def argument (i j : ℕ) : ℚ :=
  let k := 155-i
  let b : ℚ := 506-j
  506*3.401937574248-0.693147180559+b/2-floorLog i+cum k-cum (k-j) +
    b*max 0 (logCap (k-j)-widthLog j) + 505*0.0000000001 + 26*2.302585092995

private theorem charge_units (u : FlagIndex) : flagCharge u * 10^26 ≤ units u.1.val u.2.val := by
  let i := u.1.val
  let j := u.2.val
  let k := 155-i
  let p := 505-j
  let w := flagCap (k-j)
  let z := max 1 (w * sqrt (2*π/(p+1:ℝ)))
  have hi : i < 154 := u.1.isLt
  have hj : j < 155-i := u.2.isLt
  have hp : (p:ℝ) = 505-j := by dsimp [p]; rw [Nat.cast_sub (by omega),Nat.cast_ofNat]
  have hb : 0 < (p+1:ℝ) := by positivity
  have hz₁ : 1 ≤ z := le_max_left .. 
  have hz : 0 < z := zero_lt_one.trans_le hz₁
  have hw : 0 < w := by
    have h (m : ℕ) : 0 < flagCap m := by
      induction m with
      | zero => exact zero_lt_one
      | succ m ih => exact ih.trans_le (le_max_left ..)
    exact h _
  have ha : planeRadius = sqrt (2704/3) := by
    unfold planeRadius areaCut
    rw [mul_div_assoc',div_div,← sq,sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  have ht : 30 ≤ planeRadius := ha ▸ le_sqrt_of_sq_le (by norm_num)
  have ht₀ : 0 < planeRadius := by linarith
  have logR : log planeRadius ≤ 3.401937574248 := by
    rw [ha,log_sqrt (by norm_num)]
    have h := log_upper (a:=2704/3) (b:=2*3.401937574248) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    push_cast at h
    linarith
  have log₂ : (0.693147180559:ℝ) ≤ log 2 := by
    simpa using (log_lower (a:=0.693147180559) (b:=2) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
  have log₁₀ : log 10 ≤ 2.302585092995 := by
    simpa using (log_upper (a:=10) (b:=2.302585092995) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  have width : log z ≤ max 0 ((logCap (k-j):ℝ)-widthLog j) := by
    rcases max_choice 1 (w*sqrt (2*π/(p+1:ℝ))) with h | h
    · change log (max _ _) ≤ _; rw [h,log_one]; exact le_max_left .. 
    · change log (max _ _) ≤ _; rw [h,log_mul hw.ne' (by positivity)]
      apply le_trans _ (le_max_right ..)
      have h' : (p+1:ℝ) = 506-j := by linarith
      rw [h']
      exact add_le_add (log_flagCap _ (by dsimp [k]; omega)) (width_le j (by omega)) |>.trans_eq (by ring)
  have quadratic : π*w^2/z^2 ≤ (p+1:ℝ)/2 := by
    have h := pow_le_pow_left₀ (mul_nonneg hw.le (sqrt_nonneg _)) (le_max_right 1
      (w*sqrt (2*π/(p+1:ℝ)))) 2
    change _ ≤ z^2 at h
    rw [mul_pow,sq_sqrt (by positivity),mul_div_assoc',div_le_iff₀ hb] at h
    apply (div_le_iff₀ (sq_pos_of_pos hz)).mpr
    linarith only [h]
  have hθ : 0 < terminalTheta (planeRadius*z) ∧ log (terminalTheta (planeRadius*z)) ≤ 0.0000000001 := by
    let y := planeRadius*z
    have hy : 30 ≤ y := by exact (by norm_num : (30:ℝ)=30*1) ▸ mul_le_mul ht hz₁ zero_le_one ht₀.le
    have ha' : 40 ≤ π*y^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr pi_gt_three.le) (sq_nonneg y),sq_nonneg (y-30)]
    have E : (10:ℝ)^12 ≤ exp 40 := by
      have h := pow_le_pow_left₀ (by norm_num : 0 ≤ (2:ℝ))
        (by linarith [add_one_le_exp (1:ℝ)] : (2:ℝ) ≤ exp 1) 40
      rw [← exp_nat_mul] at h
      norm_num at h ⊢
      linarith
    have hneg : exp (-π*y^2) ≤ 1/10^12 := by
      rw [neg_mul,exp_neg,inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (E.trans (exp_le_exp.mpr ha'))
    have hneg' : exp (-3*π*y^2) ≤ 1/10^12 :=
      (exp_le_exp.mpr (by linarith : -3*π*y^2 ≤ -π*y^2)).trans hneg
    have hd : 0 < 1-exp (-3*π*y^2) := by linarith
    have ht' : 0 < terminalTheta y := by unfold terminalTheta; positivity
    refine ⟨ht',(log_le_sub_one_of_pos ht').trans ?_⟩
    change 1+2*exp (-π*y^2)/(1-exp (-3*π*y^2))-1 ≤ _
    rw [add_sub_cancel_left]
    apply (div_le_iff₀ hd).mpr; linarith
  have H : 0 < flagCharge u := by
    change 0 < planeRadius^506/2*exp _*z^(p+1)*terminalTheta (planeRadius*z)^p
    positivity [hθ.1]
  have hlog : log (flagCharge u * 10^26) ≤ (argument i j:ℝ) := by
    change log (planeRadius^506/2*exp (π*w^2/z^2-terminalLogFloor i+logCaps k-logCaps (k-j))*
      z^(p+1)*terminalTheta (planeRadius*z)^p * 10^26) ≤ _
    rw [log_mul (by positivity [hθ.1]) (by positivity),
      log_mul (by positivity) (pow_ne_zero p hθ.1.ne'),log_mul (by positivity) (by positivity),
      log_mul (by positivity) (exp_pos _).ne',log_div (by positivity) (by norm_num)]
    simp only [log_pow,log_exp,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    unfold argument
    push_cast
    have h₁ := mul_le_mul_of_nonneg_left width hb.le
    have h₂ := mul_le_mul_of_nonneg_left hθ.2 (Nat.cast_nonneg p : 0 ≤ (p:ℝ))
    have h₃ := caps_diff (k-j) k (Nat.sub_le ..) (by dsimp [k]; omega)
    have h₄ := floor_le i (by omega)
    dsimp only [k] at h₁ h₃
    rw [hp] at h₁ h₂ quadratic ⊢
    dsimp only [k]
    nlinarith only [h₁,h₂,h₃,h₄,quadratic,hp,logR,log₂,log₁₀,(Nat.cast_nonneg j : 0 ≤ (j:ℝ))]
  have cert : ∀ (i : Fin 154) (j : Fin (155-i.val)),
    let x := argument i j
    if x ≤ 0 then 1 ≤ units i j else x/32 ≤ 1 ∧ up (x/32)^32 ≤ (units i j:ℚ) := by decide +kernel
  have hc := cert u.1 u.2
  change (if argument i j ≤ 0 then _ else _) at hc
  rw [← exp_log (mul_pos H (by positivity))]
  apply (exp_le_exp.mpr hlog).trans
  split at hc
  · exact ((exp_le_one_iff.mpr (by exact_mod_cast ‹argument i j ≤ 0›))).trans (by exact_mod_cast hc)
  · obtain ⟨hh,hh'⟩ := hc
    apply (exp_up (n:=32) (by decide +kernel) (div_nonneg (le_of_not_ge ‹¬argument i j ≤ 0›) (by norm_num))
      (by simpa using hh)).trans
    exact_mod_cast hh'

theorem flagCharge_sum : (∑ u : FlagIndex, flagCharge u) ≤ 5.28399/(10:ℝ)^15 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun u _ ↦ charge_units u)
  rw [← Finset.sum_mul] at h
  have hc : (∑ i : Fin 154, ∑ j : Fin (155-i.val), units i j) ≤ 528399000000 := by decide +kernel
  have ht : (∑ u : FlagIndex, (units u.1 u.2:ℝ)) ≤ 528399000000 := by
    rw [Fintype.sum_sigma]
    exact_mod_cast hc
  linarith only [h,ht]

end SigabaNeo.Wall1.ControlledPlane.FlagEnvelope

#print axioms SigabaNeo.Wall1.ControlledPlane.FlagEnvelope.flagCharge_sum
