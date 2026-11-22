module

public import N14.Energy.Singular
public import N14.Energy.Untyped
public import N14Cert.Case0Close.Run
public import N14Cert.Case0Pos.Run
public import N14.Energy.Pair
public import N14Cert.Case0Pos.Slack
public import N14Cert.Case0Close.Slack
import CAP.Transport.Hex

@[expose] public section

namespace N14Cert.Case0Id

open N14.Ident N14.Energy CAP.ThreePoint N14.Box Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 100000

/-- The parameters of the identities: Kronecker slot width `W` (that of the runs), slot width `w` and bias
exponent `a` of the matrices. -/
noncomputable def P : CAP.ThreePoint.Params :=
  { N := 14, D := 8, W := 408, w := 114, a := 100, aH := 1, eb := 2, cb := 1 }

/-- The block `k = 0` of the kernel rooted at a point of the type 0: order 9, 9 basis functions of the type 0. -/
noncomputable def blk0_0 : Blk := ⟨9, 9, hex% "890376e9eaff7e5092ed0400000021e94db9c9896870000000000000086cbfde9f030d27424bb41000000190ba8b63628decf6d12fc00000007c8fa7a3ae6cd200000000000000264b60b625acf713d538b8100000076868f17cedacd300000000000001c1f473b2ea5855a5fdc272000000857faea9188ca5c000000000000022395e2729dae35dbcb24ac8000008bdd2ac112e230496f508a0000001fb84c81f290245c000000000000069100335660aee6605d27b4000002029e0bbe2ffac2b000000000000085d46c7eb61619e00ace97d4000020988d8a3282c352000000000000083d74aa86e78b3eb4047b1c000001fdc6d203abb01dc00000000000007bda6ca9a3a0bb9429c546c80000200edd17cd685742800000000000081265680c918fb9e37da625e0000206227cec1b7a627eda25f80000007f65429283dbba180000000000001f12fcba37757c23cf506b92000008089022b5e74ec420000000000002063f5017387b4d000e1c103000007f8b62133b885600000000000000200f321ea31eccdf91acaefe200007fb18ac474604c4f000000000000204694eaa7583fa3a5fdc2720000080409f1f5eba016c0000000000001f9c94ec163174529fdfbfdb000007e8b13ec8ca3bcf9c000000000001fa5c199b9342156dabd7ac040000804e77c4f8358c65a000000000002052436aa37d882e897035c5500007ef1fa312010cedd424bb41000001ff42fc9d8d8f595600000000000081c5e8599a2f9c55aad5aadc0000200f8db5b797c86eb8000000000007f1f31aaf50b491bffdfbfdb00001ff58a12d3387931d4000000000007fe7641dda0afebbc8ec83988000200bce7381fbfc4bb9800000000008009b96fc40ba8773e4b7a845"⟩

theorem psd0_0 : CAP.PSD.check { n := 9, w := 114, a := 100, aL := 53, p2 := 4, e := 48, nb := 4 } blk0_0.rows
    (hex% "100000d5f36eaa0000000000000003ffffd4abb5e900000000000000010000cbc18d6ff0000000000000003fff8383b40344000000000000000fffeb9eb83ddc00000000000000040007175626ac0000000000000000fffa9d2cc81b40000000000000003ffe4fc8c9ff2c00000000000000100050b845498e000000000000000400127d79d7f18000000000000001000f6c6a438c30000000000000003fffe061928fa8000000000000000ffde7dfd0d7b5000000000000000400035520ebc54000000000000001000fae36d863b00000000000000042539ff1154cdc00000000000000123b0a68c4adde000000000000000427a5ec4d900f0000000000000000d90aa7b24a64c0000000000000003c226573b40d380000000000000010d715eb799b300000000000000003cc6c4c42e3c20000000000000000d58f01ce8db9e0000000000000003c4ebf7fb602d00000000000000012fcab95fe17ba000000000000000426684924119d8000000000000000f210f4e1364b400000000000000041dbcd3f7582b800000000000000118c2ca16c132d00000000000000044421d969c7d60000000000000000d37dd0b29d8760000000000000003a1d79a3891a34000000000000001076b589c9e6290000000000000003d37eae5d1a8d400000000000000105edec82173a100000000000000045d3f1be2068d4000000000000000c2c576fb0c6ed0000000000000003d523fad30e9b000000000000000166ecdd0c86bc80000000000000004386de19b33840000000000000000cd063f46cf2440000000000000003da0c529d9663c000000000000000fa6b7a580362500000000000000042ad5a235378b40000000000000010468fa6438359") = true := by
  decide +kernel

/-- The block `k = 1` of the kernel rooted at a point of the type 0: order 8, 8 basis functions of the type 0. -/
noncomputable def blk0_1 : Blk := ⟨8, 8, hex% "27f0362c66f8d88d092ed04000000b707c19f05d21c00000000000000286d166082971893424bb410000004bc0d8ed04aa7c497f709c8000001810a679e41c29c000000000000009a7ed051d30f63d2f2c92b2000001362f96e1b33e5800000000000000429ea8040e4da918e4738f4000002740e72e787ddb6000000000000009cf6e6303b23cb32253c419400001ef20a36da5c4b56d011ec700000071ac5801017618800000000000001ed13f91f48a877c0a7151b2000008e3bca2e3587d14000000000000021004d462c5ca66fcdf6989780000833f0b121ed11b8000000000000020ba9026987a6fd5aa952a92000007e00cf83823045200000000000001ee2da2223629e9517d6c9a3000007e504bd44b8a8750000000000000203b3361da347209df60faee20000848143c08aa3618497f709c80000202c6dae2b358d3a00000000000007aad27795f502403ff7eff6c00001f64df9f0fc6055d00000000000007f7fd704b7c7c3852af5eb010000207449ca1126d96ca0000000000008187612644e5afbc61c0d71540001fe8ce9c3c6c881200000000000007fcbe2080a33e4cb2f6d12fc00001fe5c6c27c881c5480000000000007fa6cec4d656c5206d011ec70000201c2ed3444a982cc00000000000080152640cd5af7fac97f709c800020056efa07c87ac8780000000000080abdd90eb9ab2304d092ed04"⟩

theorem psd0_1 : CAP.PSD.check { n := 8, w := 114, a := 100, aL := 51, p2 := 0, e := 48, nb := 4 } blk0_1.rows
    (hex% "10000bd1494a8c000000000000000400018774614b000000000000000100028b02e209c0000000000000003ffc11bf6abbe0000000000000000fff876fa276100000000000000004004ef6a774d30000000000000000890ab1b9755ac000000000000000263b5deea6288000000000000000164cf42b6d24740000000000000005616eafc7a8130000000000000000f0319fea1e8bc0000000000000002f3f418c634790000000000000000e8595b545a33c0000000000000004eccee05327bd00000000000000012494d1f0e86cc00000000000000042a61da28e43e00000000000000012dbe1de145bf4000000000000000455948ffe704a0000000000000000c9211d56f9b58000000000000000399e0623795e500000000000000010e090ea7732480000000000000004a5ddf14853f400000000000000010679b52215d2800000000000000033dee68380ea60000000000000000ea00f720412500000000000000003eca40c8a591800000000000000011097b0f05e0cc00000000000000046fd0236424ad0000000000000000faff02355fa900000000000000003f4c178a70cba0000000000000000fa579e71ba7380000000000000003ecc1bb6d8c090000000000000001061499164ff28000000000000000404901fec3abf0000000000000001012c1a659174c00000000000000044a28f1699361") = true := by
  decide +kernel

/-- The block `k = 2` of the kernel rooted at a point of the type 0: order 7, 7 basis functions of the type 0. -/
noncomputable def blk0_2 : Blk := ⟨7, 7, hex% "251021ec1fc44d93424bb41000000913fdb5c306be000000000000000214dde9dd8ac9144d092ed04000005fa5b7ae19d5f518e4738f4000001d1c66eca5a3ac0000000000000008dc07fdd87b562b2253c419400001c4262087aa42d70000000000000077528f917fd3d20fda42bdd80000229b6da0bd100e18000000000000083f467b329fd781f4bbb049a0000201232afe49ec185aa952a92000007d503ffff22aa6000000000000001f765b023c906ecd17d6c9a300000822328387b9c06040000000000002056d4003e7db018df60faee2000080b1346ee09cbba80000000000001fb1c75aa012b26b025bd422800007e406cf28cc4716400000000000020054b7c74a78b48c97f709c80000815251982f586064800000000000203a03e11704b331e88416678c00080dacbb8f64e6fcb2f6d12fc00001fe5bff4cad91d8200000000000007eae85fcd332db2f6d011ec700002010b53ba3fe5e190000000000000808fe42543b516e5c97f709c80002010ebcaabf1f978900000000000080314ce5146e125c2d092ed04"⟩

theorem psd0_2 : CAP.PSD.check { n := 7, w := 114, a := 100, aL := 51, p2 := 0, e := 46, nb := 3 } blk0_2.rows
    (hex% "100005f46840d4000000000000000400047243d3c600000000000000010001a53f91bb00000000000000003ffd93317295f0000000000000000ffff5e2e99d6800000000000000040023041a063100000000000000009d978f3cdaf3c00000000000000034e8fb2360c3200000000000000014be82cb8d5e6c0000000000000004936fe38b32a60000000000000000f1f0bbd9227580000000000000003aae8f6ae244c000000000000000103873caeac7e80000000000000004638dfdb545c9000000000000000112a27a1869c4000000000000000040549822f83d10000000000000000f43787b5611180000000000000003d5bd6ad250ee0000000000000000fecaa21e9077000000000000000042ee29cd8c75f0000000000000001146fcce6efb54000000000000000458231a6e49fb0000000000000000f56cfa04aa8f80000000000000003780e0d75e895000000000000000106bafd7df0820000000000000000439f6a3b34b84000000000000000106d0f7ce7077c000000000000000427b81b057f7a") = true := by
  decide +kernel

/-- The block `k = 3` of the kernel rooted at a point of the type 0: order 6, 6 basis functions of the type 0. -/
noncomputable def blk0_3 : Blk := ⟨6, 6, hex% "819ab6d1fe512383424bb41000001ff4ad6725e50fb9800000000000080c512b372f1a59cd092ed0400001f942cc1fd3fe5d5f690af760000080e6fefe967cdb70800000000000202a8b319b3d4d5592eec126800007f5bd8ca10c446c20000000000001fe214a4b1179c9997b6897e0000080151189f272e2fb8000000000002009a6be64a1bb27476706f5100007f5678a62fc11989096f508a00001fdbb3b97eb66230c4000000000007ff8e43894be294325fdc27200002012a63b712fd0ab1c000000000008048340777ebed769210599e30001ff5748285850bde30000000000007fcad23186d1d2433424bb4100002000275f6315777b040000000000080202bc28a3f64a27ed215eec00020010aff22c2a3582880000000000800c3aa0c6531cfe19c6e31c3"⟩

theorem psd0_3 : CAP.PSD.check { n := 6, w := 114, a := 100, aL := 49, p2 := 0, e := 45, nb := 3 } blk0_3.rows
    (hex% "100092ed7f21d00000000000000004001a5155aa380000000000000001001b4791be2e00000000000000003fdaa249a19440000000000000001005530cc29840000000000000000401dfc14bd70c0000000000000000a0e5e41d228400000000000000004c3acd6aee87c000000000000000149c07980f04a00000000000000004149751c93e040000000000000000c9d4ca02cbc5000000000000000034a500ce597cc0000000000000000fd97cca77a97000000000000000045c3e906e838c00000000000000012ff2f995b08d000000000000000037789c94c2bb00000000000000000d4fcf2aa36b00000000000000000401fd85c3bf7800000000000000011a0534f4d55a000000000000000040d7f36e00680000000000000000113c832c58eac") = true := by
  decide +kernel

/-- The block `k = 4` of the kernel rooted at a point of the type 0: order 5, 5 basis functions of the type 0. -/
noncomputable def blk0_4 : Blk := ⟨5, 5, hex% "8307d93cc26590c4d092ed04000020c535bf04161d48000000000000080d2a7de4ed0f6393424bb4100001f93fd3bf7d4bd7d97b6897e000007f294fdbb0321420000000000000200f301957043597476706f5100007f36fc3e942151a80000000000001fdf65abfe1d272e8c7239c7a00008031150a5cf373080000000000002008298c307d3eca1025bd42280007feb066ad68bfdf13424bb4100001ffe5d1676e202f100000000000008006d84d6e00265e7ed215eec0001fff3f50c3993850400000000000080008f43fd1dbbeb39c6e31c3"⟩

theorem psd0_4 : CAP.PSD.check { n := 5, w := 114, a := 100, aL := 50, p2 := 0, e := 44, nb := 3 } blk0_4.rows
    (hex% "20002bd928cb60000000000000000800107a7474000000000000000002000abc7432e700000000000000007fe4ff0f0bc0c0000000000000001ffd58866ec6800000000000000008007ff6f063bc000000000000000177d89e80d02c00000000000000006c6dc6f603854000000000000000223b262c74df60000000000000000879024de0d2ec0000000000000001b0b232d3ea10000000000000000079d0238c9e2b8000000000000000219e1434b245d00000000000000007d277b2578f840000000000000002043b57c240c3") = true := by
  decide +kernel

/-- The block `k = 5` of the kernel rooted at a point of the type 0: order 4, 4 basis functions of the type 0. -/
noncomputable def blk0_5 : Blk := ⟨4, 4, hex% "204399d67c67f5744d092ed040000804936ed89c6876c00000000000020021a566056f43ff3424bb4100007f7f689837b98c1631c8e71e80001ffb313af090e39bc000000000000800f87387ba95f43c096f508a0001fff5bfa954811ae80000000000007ffddf9888b1d40032f6d12fc000200045070b677caba00000000000080003c35cdf488e9668497682"⟩

theorem psd0_5 : CAP.PSD.check { n := 4, w := 114, a := 100, aL := 49, p2 := 0, e := 43, nb := 3 } blk0_5.rows
    (hex% "40003a361afa40000000000000000fffcc563d1ff000000000000000040009099d9e4c0000000000000000a43008ece7cd00000000000000003d50a5d0e56c400000000000000011562a8583b0a00000000000000003c4366a93a7180000000000000000f398f1818408000000000000000041929480bc594000000000000000102be4fcc850e") = true := by
  decide +kernel

/-- The block `k = 6` of the kernel rooted at a point of the type 0: order 3, 3 basis functions of the type 0. -/
noncomputable def blk0_6 : Blk := ⟨3, 3, hex% "2007f4e3dc7a339e93424bb4100007ffc3378c0ecd587c00000000000200007415d2d6099ef5092ed040007ff8cb2d2b267f2cb2f6d12fc00020001b8699133ede6c000000000008000686de26ebff2e68497682"⟩

theorem psd0_6 : CAP.PSD.check { n := 3, w := 114, a := 100, aL := 47, p2 := 0, e := 41, nb := 2 } blk0_6.rows
    (hex% "1000210b5c148000000000000000040005939fac3000000000000000010000ea11b674000000000000000020164005dba900000000000000001079e5a9d19440000000000000000439cec878c52") = true := by
  decide +kernel

/-- The block `k = 7` of the kernel rooted at a point of the type 0: order 2, 2 basis functions of the type 0. -/
noncomputable def blk0_7 : Blk := ⟨2, 2, hex% "8002d378801aa69b13424bb410002000068fd203dd6ccf800000000008000003cf19e5e4c45284bb41"⟩

theorem psd0_7 : CAP.PSD.check { n := 2, w := 114, a := 100, aL := 46, p2 := 0, e := 35, nb := 2 } blk0_7.rows
    (hex% "20077b02d45a00000000000000000a609da2d10940000000000000000202c293c277e") = true := by
  decide +kernel

/-- The block `k = 8` of the kernel rooted at a point of the type 0: order 1, 1 basis functions of the type 0. -/
noncomputable def blk0_8 : Blk := ⟨1, 1, hex% "800000000074efc449d47cc41"⟩

theorem psd0_8 : CAP.PSD.check { n := 1, w := 114, a := 100, aL := 32, p2 := 0, e := 1, nb := 1 } blk0_8.rows
    (3171767210) = true := by
  decide +kernel

/-- The blocks of the kernel rooted at a point of the type 0. -/
noncomputable def blocks0 : List Blk := [blk0_0, blk0_1, blk0_2, blk0_3, blk0_4, blk0_5, blk0_6, blk0_7, blk0_8]

/-- The quadratic forms of these blocks are nonnegative. -/
theorem blocks0_pd : BlkPD P blocks0 :=
  blkPD_cons (blk_posDef P _ blk0_0 _ rfl rfl rfl psd0_0) <|
  blkPD_cons (blk_posDef P _ blk0_1 _ rfl rfl rfl psd0_1) <|
  blkPD_cons (blk_posDef P _ blk0_2 _ rfl rfl rfl psd0_2) <|
  blkPD_cons (blk_posDef P _ blk0_3 _ rfl rfl rfl psd0_3) <|
  blkPD_cons (blk_posDef P _ blk0_4 _ rfl rfl rfl psd0_4) <|
  blkPD_cons (blk_posDef P _ blk0_5 _ rfl rfl rfl psd0_5) <|
  blkPD_cons (blk_posDef P _ blk0_6 _ rfl rfl rfl psd0_6) <|
  blkPD_cons (blk_posDef P _ blk0_7 _ rfl rfl rfl psd0_7) <|
  blkPD_cons (blk_posDef P _ blk0_8 _ rfl rfl rfl psd0_8) <|
  blkPD_nil P

/-- The data of the certificate for the run `N14Cert.Case0Close.run`. -/
noncomputable def certCase0Close : UCert :=
  { P := P, blocks := blocks0, R := N14Cert.Case0Close.run,
    U1 := N14Cert.Case0Close.tab0, U2 := N14Cert.Case0Close.tab0, U3 := N14Cert.Case0Close.tab1,
    N := 14, cM := 2, cK := 1, wB := 148, aB := 148,
    B := hex% "5fffffffffffff612f04a6e6fae7ad775e19c5ffffffffffffec361566c69cd58f425da0805fffffffffffffdbd64aa14de10cc112a850860000000000001ecfdcb2ec29135ed50af760600000000000016fb14a9fd54ac3d0a7af0246000000000000008149c6a57e0c04b208f638600000000000005ba794eb3f2317baaa4194860000000000000e0e5ba0aa6c9862462d12fc8000000000000000000000000000000000000",
    cp := 0, cn := hex% "600000000000014a8c8cf68e4dd5e9e986f6e",
    kp := 0, kn := hex% "14cbd961931a91ce3ba9ead5e7b8",
    fS := hex% "444000000000000000000000000" }

/-- The kernel accepts the identity of the run: its mixed part is that of the six kernels. -/
theorem certCase0Close_id3 : id3Ok P certCase0Close.id3 = true := by decide +kernel

/-- The kernel accepts the identity of a pair. -/
theorem certCase0Close_id1 : id1Ok P certCase0Close.id1 = true := by decide +kernel

/-- The sums of the coefficients of the two parts of the kernel: its value at `(1, 1, 1)`. -/
theorem certCase0Close_one : kern P ⟨0, 0, 0⟩ 0 blocks0 = (hex% "242cc6be75008af6ee0cb98162aeab", hex% "242cc6abc7713f9de948572c181962") := by
  decide +kernel

theorem certCase0Close_ok : certCase0Close.Ok :=
  { h3 := certCase0Close_id3, h1 := certCase0Close_id1, hW := rfl, hPD := blocks0_pd,
    hc1 := by decide, hcM := by decide, hN := by decide,
    hT2 := fun s => tabFn_congr _ _ rfl rfl rfl rfl rfl rfl s,
    hT3 := fun s => tabFn_congr _ _ rfl rfl rfl rfl rfl rfl s }

/-- The data of the certificate for the run `N14Cert.Case0Pos.run`. -/
noncomputable def certCase0Pos : UCert :=
  { P := P, blocks := blocks0, R := N14Cert.Case0Pos.run,
    U1 := N14Cert.Case0Pos.tab0, U2 := N14Cert.Case0Pos.tab0, U3 := N14Cert.Case0Pos.tab0,
    N := 14, cM := 2, cK := 1, wB := 148, aB := 148,
    B := hex% "5fffffffffffff612f04a6e6fae7ad775e19c5ffffffffffffec361566c69cd58f425da0805fffffffffffffdbd64aa14de10cc112a850860000000000001ecfdcb2ec29135ed50af760600000000000016fb14a9fd54ac3d0a7af0246000000000000008149c6a57e0c04b208f638600000000000005ba794eb3f2317baaa4194860000000000000e0e5ba0aa6c9862462d12fc8000000000000000000000000000000000000",
    cp := 0, cn := hex% "60000000000000ec8bbb3f76f4f1e9e986f6e",
    kp := 0, kn := hex% "139f1cc2a65ae06ccfa9ead5e7b8",
    fS := hex% "444000000000000000000000000" }

/-- The kernel accepts the identity of the run: its mixed part is that of the six kernels. -/
theorem certCase0Pos_id3 : id3Ok P certCase0Pos.id3 = true := by decide +kernel

/-- The kernel accepts the identity of a pair. -/
theorem certCase0Pos_id1 : id1Ok P certCase0Pos.id1 = true := by decide +kernel

/-- The sums of the coefficients of the two parts of the kernel: its value at `(1, 1, 1)`. -/
theorem certCase0Pos_one : kern P ⟨0, 0, 0⟩ 0 blocks0 = (hex% "242cc6be75008af6ee0cb98162aeab", hex% "242cc6abc7713f9de948572c181962") := by
  decide +kernel

theorem certCase0Pos_ok : certCase0Pos.Ok :=
  { h3 := certCase0Pos_id3, h1 := certCase0Pos_id1, hW := rfl, hPD := blocks0_pd,
    hc1 := by decide, hcM := by decide, hN := by decide,
    hT2 := fun s => tabFn_congr _ _ rfl rfl rfl rfl rfl rfl s,
    hT3 := fun s => tabFn_congr _ _ rfl rfl rfl rfl rfl rfl s }

/-- The stored cutoff `0.8` of the source, a binary64 number. -/
noncomputable def tHigh : ℝ := (8106479329266893 : ℝ) / 4503599627370496 - 1

/-- The slack function is nonnegative at ordered arguments of the Gram domain. -/
theorem certCase0Pos_sorted (u v t : ℝ) (huv : u ≤ v) (hvt : v ≤ t) (hu : -1 ≤ u) (ht1 : t < 1)
    (hg : 0 ≤ gram u v t) : 0 ≤ certCase0Pos.lam u v t := by
  refine N14Cert.Case0Pos.slack_nonneg u v t hu (by linarith) (by linarith) ?_
  refine ⟨by linarith, by linarith, ht1, hg, ?_, ?_⟩
  · intro cut hc
    have hc' : cut ∈ [{ kind := 2, a := 1, b := 0, vn := 0, vd := 1 }, { kind := 2, a := 2, b := 1, vn := 0, vd := 1 }] := hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl <;> simp [cutVal, co] <;> linarith
  · intro Pp hPp
    exact absurd (show Pp ∈ ([] : List ℕ) from hPp) List.not_mem_nil

/-- The slack function minus the threshold `c` is nonnegative at ordered arguments of the Gram domain whose
largest one is at least `tHigh`. -/
theorem certCase0Close_sorted (u v t : ℝ) (huv : u ≤ v) (hvt : v ≤ t) (hu : -1 ≤ u) (ht1 : t < 1)
    (hg : 0 ≤ gram u v t) (hc : tHigh ≤ t) : 0 ≤ certCase0Close.lam u v t := by
  unfold tHigh at hc
  refine N14Cert.Case0Close.slack_nonneg u v t hu (by linarith) (by linarith) ?_
  refine ⟨by linarith, by linarith, ht1, hg, ?_, ?_⟩
  · intro cut hc
    have hc' : cut ∈ [{ kind := 2, a := 1, b := 0, vn := 0, vd := 1 }, { kind := 2, a := 2, b := 1, vn := 0, vd := 1 }, { kind := 0, a := 2, b := 0, vn := 8106479329266893, vd := 4503599627370496 }] := hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl <;> simp [cutVal, co] <;> linarith
  · intro Pp hPp
    exact absurd (show Pp ∈ ([] : List ℕ) from hPp) List.not_mem_nil

/-- **Case 0: a configuration of 14 points of the unit sphere with two points whose inner product is at least
`tHigh` has Coulomb energy at least `e₀ + 3 c`** (the offset of the certificate plus three times its
threshold; the number is their sum). -/
theorem energy_ge (x : Fin 14 → EuclideanSpace ℝ (Fin 3)) (hx : ∀ i, ‖x i‖ = 1)
    (hinj : Function.Injective x) (i0 j0 : Fin 14) (h : i0 ≠ j0) (ht : tHigh ≤ inner ℝ (x i0) (x j0)) :
    (5120257112054960846081 : ℝ) / 73786976294838206464
      ≤ ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / dist (x i) (x j) := by
  have hC := certCase0Pos_ok
  have hC' := certCase0Close_ok
  have hmain := certCase0Pos.energy_pair certCase0Close hC hC' rfl rfl rfl rfl rfl rfl rfl _ _ 5110096645419161624321 73786976294838206464
    5120257112054960846081 73786976294838206464 certCase0Pos_one (by decide) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) x hx i0 j0 h
    (fun i j k hd => lam_region certCase0Pos hC (fun _ => True) 0
      (fun u v t huv hvt hu ht1 hg _ _ _ => certCase0Pos_sorted u v t huv hvt hu ht1 hg) x hx hinj i j k hd
      trivial trivial trivial)
    (fun i j k hd c1 c2 => lam_region3 certCase0Close hC' (fun u v t => tHigh ≤ u ∨ tHigh ≤ v ∨ tHigh ≤ t)
      (fun u v t hr => by tauto) (fun u v t hr => by tauto) 0
      (fun u v t huv hvt hu ht1 hg hr => certCase0Close_sorted u v t huv hvt hu ht1 hg
        (by rcases hr with hr | hr | hr <;> linarith)) x hx hinj i j k hd (by
        rcases c1 with rfl | rfl | rfl <;> rcases c2 with rfl | rfl | rfl
        · exact absurd rfl h
        · exact Or.inl ht
        · exact Or.inr (Or.inl ht)
        · exact Or.inl (ht.trans (le_of_eq (real_inner_comm _ _)))
        · exact absurd rfl h
        · exact Or.inr (Or.inr ht)
        · exact Or.inr (Or.inl (ht.trans (le_of_eq (real_inner_comm _ _))))
        · exact Or.inr (Or.inr (ht.trans (le_of_eq (real_inner_comm _ _))))
        · exact absurd rfl h))
  push_cast at hmain
  exact hmain

/-- info: 'N14Cert.Case0Id.energy_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms energy_ge

end N14Cert.Case0Id
