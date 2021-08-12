use super::{Mds, Spec};
use ff::Field;
use pasta_curves::Fq;

/// TODO
pub struct PoseidonFq;
// Vesta base
impl Spec<Fq, 3, 2> for PoseidonFq {
    fn full_rounds() -> usize {
        8
    }

    fn partial_rounds() -> usize {
        56
    }

    fn sbox(val: Fq) -> Fq {
        val.pow_vartime(&[5])
    }

    fn secure_mds(&self) -> usize {
        unimplemented!()
    }

    fn constants(&self) -> (Vec<[Fq; 3]>, Mds<Fq, 3>, Mds<Fq, 3>) {
        (ROUND_CONSTANTS[..].to_vec(), MDS, MDS_INV)
    }
}

// $ sage generate_parameters_grain.sage 1 0 255 3 8 56 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001
// Number of round constants: 192
// Round constants for GF(q):
pub(crate) const ROUND_CONSTANTS: [[Fq; 3]; 64] = [
    [
        Fq::from_raw([
            0x5753_8c25_9642_6303,
            0x4e71_162f_3100_3b70,
            0x353f_628f_76d1_10f3,
            0x360d_7470_611e_473d,
        ]),
        Fq::from_raw([
            0xbdb7_4213_bf63_188b,
            0x4908_ac2f_12eb_e06f,
            0x5dc3_c6c5_febf_aa31,
            0x2bab_94d7_ae22_2d13,
        ]),
        Fq::from_raw([
            0x0939_d927_53cc_5dc8,
            0xef77_e7d7_3676_6c5d,
            0x2bf0_3e1a_29aa_871f,
            0x150c_93fe_f652_fb1c,
        ]),
    ],
    [
        Fq::from_raw([
            0x1425_9dce_5377_82b2,
            0x03cc_0a60_141e_894e,
            0x955d_55db_56dc_57c1,
            0x3270_661e_6892_8b3a,
        ]),
        Fq::from_raw([
            0xce9f_b9ff_c345_afb3,
            0xb407_c370_f2b5_a1cc,
            0xa0b7_afe4_e205_7299,
            0x073f_116f_0412_2e25,
        ]),
        Fq::from_raw([
            0x8eba_d76f_c715_54d8,
            0x55c9_cd20_61ae_93ca,
            0x7aff_d09c_1f53_f5fd,
            0x2a32_ec5c_4ee5_b183,
        ]),
    ],
    [
        Fq::from_raw([
            0x2d8c_cbe2_92ef_eead,
            0x634d_24fc_6e25_59f2,
            0x651e_2cfc_7406_28ca,
            0x2703_26ee_039d_f19e,
        ]),
        Fq::from_raw([
            0xa068_fc37_c182_e274,
            0x8af8_95bc_e012_f182,
            0xdc10_0fe7_fcfa_5491,
            0x27c6_642a_c633_bc66,
        ]),
        Fq::from_raw([
            0x9ca1_8682_e26d_7ff9,
            0x710e_1fb6_ab97_6a45,
            0xd27f_5739_6989_129d,
            0x1bdf_d8b0_1401_c70a,
        ]),
    ],
    [
        Fq::from_raw([
            0xc832_d824_261a_35ea,
            0xf4f6_fb3f_9054_d373,
            0x14b9_d6a9_c84d_d678,
            0x162a_14c6_2f9a_89b8,
        ]),
        Fq::from_raw([
            0xf798_2466_7b5b_6bec,
            0xac0a_1fc7_1e2c_f0c0,
            0x2af6_f79e_3127_feea,
            0x2d19_3e0f_76de_586b,
        ]),
        Fq::from_raw([
            0x5d0b_f58d_c8a4_aa94,
            0x4fef_f829_8499_0ff8,
            0x8169_6ef1_104e_674f,
            0x044c_a3cc_4a85_d73b,
        ]),
    ],
    [
        Fq::from_raw([
            0x6198_785f_0cd6_b9af,
            0xb8d9_e2d4_f314_f46f,
            0x1d04_5341_6d3e_235c,
            0x1cba_f2b3_71da_c6a8,
        ]),
        Fq::from_raw([
            0x343e_0761_0f3f_ede5,
            0x293c_4ab0_38fd_bbdc,
            0x0e6c_49d0_61b6_b5f4,
            0x1d5b_2777_692c_205b,
        ]),
        Fq::from_raw([
            0xf60e_971b_8d73_b04f,
            0x06a9_adb0_c1e6_f962,
            0xaa30_535b_dd74_9a7e,
            0x2e9b_dbba_3dd3_4bff,
        ]),
    ],
    [
        Fq::from_raw([
            0x035a_1366_1f22_418b,
            0xde40_fbe2_6d04_7b05,
            0x8bd5_bae3_6969_299f,
            0x2de1_1886_b180_11ca,
        ]),
        Fq::from_raw([
            0xbc99_8884_ba96_a721,
            0x2ab9_395c_449b_e947,
            0x0d5b_4a3f_1841_dcd8,
            0x2e07_de17_80b8_a70d,
        ]),
        Fq::from_raw([
            0x825e_4c2b_b749_25ca,
            0x2504_40a9_9d6b_8af3,
            0xbbdb_63db_d52d_ad16,
            0x0f69_f185_4d20_ca0c,
        ]),
    ],
    [
        Fq::from_raw([
            0x816c_0594_22dc_705e,
            0x6ce5_1135_07f9_6de9,
            0x0d13_5dc6_39fb_09a4,
            0x2eb1_b254_17fe_1767,
        ]),
        Fq::from_raw([
            0xb8b1_bdf4_953b_d82c,
            0xff36_c661_d26c_c42d,
            0x8c24_cb44_c3fa_b48a,
            0x115c_d0a0_643c_fb98,
        ]),
        Fq::from_raw([
            0xde80_1612_311d_04cd,
            0xbb57_ddf1_4e0f_958a,
            0x066d_7378_b999_868b,
            0x26ca_293f_7b2c_462d,
        ]),
    ],
    [
        Fq::from_raw([
            0xf520_9d14_b248_20ca,
            0x0f16_0bf9_f71e_967f,
            0x2a83_0aa1_6241_2cd9,
            0x17bf_1b93_c4c7_e01a,
        ]),
        Fq::from_raw([
            0x05c8_6f2e_7dc2_93c5,
            0xe03c_0354_bd8c_fd38,
            0xa24f_8456_369c_85df,
            0x35b4_1a7a_c4f3_c571,
        ]),
        Fq::from_raw([
            0x72ac_156a_f435_d09e,
            0x64e1_4d3b_eb2d_ddde,
            0x4359_2799_4849_bea9,
            0x3b14_8008_0523_c439,
        ]),
    ],
    [
        Fq::from_raw([
            0x2716_18d8_74b1_4c6d,
            0x08e2_8644_2a2d_3eb2,
            0x4950_856d_c907_d575,
            0x2cc6_8100_31dc_1b0d,
        ]),
        Fq::from_raw([
            0x91f3_18c0_9f0c_b566,
            0x9e51_7aa9_3b78_341d,
            0x0596_18e2_afd2_ef99,
            0x25bd_bbed_a1bd_e8c1,
        ]),
        Fq::from_raw([
            0xc631_3487_073f_7f7b,
            0x2a5e_d0a2_7b61_926c,
            0xb95f_33c2_5dde_8ac0,
            0x392a_4a87_58e0_6ee8,
        ]),
    ],
    [
        Fq::from_raw([
            0xe7bb_cef0_2eb5_866c,
            0x5e6a_6fd1_5db8_9365,
            0x9aa6_111f_4de0_0948,
            0x272a_5587_8a08_442b,
        ]),
        Fq::from_raw([
            0x9b92_5b3c_5b21_e0e2,
            0xa6eb_ba01_1694_dd12,
            0xefa1_3c4e_60e2_6239,
            0x2d5b_308b_0cf0_2cdf,
        ]),
        Fq::from_raw([
            0xef38_c57c_3116_73ac,
            0x44df_f42f_18b4_6c56,
            0xdd5d_293d_72e2_e5f2,
            0x1654_9fc6_af2f_3b72,
        ]),
    ],
    [
        Fq::from_raw([
            0x9b71_26d9_b468_60df,
            0x7639_8265_3442_0311,
            0xfa69_c3a2_ad52_f76d,
            0x1b10_bb7a_82af_ce39,
        ]),
        Fq::from_raw([
            0x90d2_7f6a_00b7_dfc8,
            0xd1b3_6968_ba04_05c0,
            0xc79c_2df7_dc98_a3be,
            0x0f1e_7505_ebd9_1d2f,
        ]),
        Fq::from_raw([
            0xff45_7756_b819_bb20,
            0x797f_d6e3_f18e_b1ca,
            0x537a_7497_a3b4_3f46,
            0x2f31_3faf_0d3f_6187,
        ]),
    ],
    [
        Fq::from_raw([
            0xf0bc_3e73_2ecb_26f6,
            0x5cad_11eb_f0f7_ceb8,
            0xfa3c_a61c_0ed1_5bc5,
            0x3a5c_bb6d_e450_b481,
        ]),
        Fq::from_raw([
            0x8655_27cb_ca91_5982,
            0x51ba_a6e2_0f89_2b62,
            0xd920_86e2_53b4_39d6,
            0x3dab_54bc_9bef_688d,
        ]),
        Fq::from_raw([
            0x3680_45ac_f2b7_1ae3,
            0x4c24_b33b_410f_efd4,
            0xe280_d316_7012_3f74,
            0x06db_fb42_b979_884d,
        ]),
    ],
    [
        Fq::from_raw([
            0xa7fc_32d2_2f18_b9d3,
            0xb8d2_de72_e3d2_c9ec,
            0xc6f0_39ea_1973_a63e,
            0x068d_6b46_08aa_e810,
        ]),
        Fq::from_raw([
            0x2b5d_fcc5_5725_55df,
            0xb868_a7d7_e1f1_f69a,
            0x0ee2_58c9_b8fd_fccd,
            0x366e_bfaf_a3ad_381c,
        ]),
        Fq::from_raw([
            0xe6bc_229e_95bc_76b1,
            0x7ef6_6d89_d044_d022,
            0x04db_3024_f41d_3f56,
            0x3967_8f65_512f_1ee4,
        ]),
    ],
    [
        Fq::from_raw([
            0xe534_c88f_e53d_85fe,
            0xcf82_c25f_99dc_01a4,
            0xd58b_7750_a3bc_2fe1,
            0x2166_8f01_6a80_63c0,
        ]),
        Fq::from_raw([
            0x4bef_429b_c533_1608,
            0xe34d_ea56_439f_e195,
            0x1bc7_4936_3e98_a768,
            0x39d0_0994_a8a5_046a,
        ]),
        Fq::from_raw([
            0x770c_956f_60d8_81b3,
            0xb163_d416_05d3_9f99,
            0x6b20_3bbe_12fb_3425,
            0x1f9d_bdc3_f843_1263,
        ]),
    ],
    [
        Fq::from_raw([
            0x9794_a9f7_c336_eab2,
            0xbe0b_c829_fe5e_66c6,
            0xe5f1_7b9e_0ee0_cab6,
            0x0277_45a9_cddf_ad95,
        ]),
        Fq::from_raw([
            0x5202_5657_abd8_aee0,
            0x2fa4_3fe2_0a45_c78d,
            0x788d_695c_61e9_3212,
            0x1cec_0803_c504_b635,
        ]),
        Fq::from_raw([
            0xd387_2a95_59a0_3a73,
            0xed50_82c8_dbf3_1365,
            0x7207_7448_ef87_cc6e,
            0x1235_23d7_5e9f_abc1,
        ]),
    ],
    [
        Fq::from_raw([
            0x0017_79e3_a1d3_57f4,
            0x27fe_ba35_975e_e7e5,
            0xf419_b848_e5d6_94bf,
            0x1723_d145_2c9c_f02d,
        ]),
        Fq::from_raw([
            0x9dab_1ee4_dcf9_6622,
            0x21c3_f776_f572_836d,
            0xfcc0_573d_7e61_3694,
            0x1739_d180_a160_10bd,
        ]),
        Fq::from_raw([
            0x7029_0452_042d_048d,
            0xfafa_96fb_eb0a_b893,
            0xacce_3239_1794_b627,
            0x2d4e_6354_da9c_c554,
        ]),
    ],
    [
        Fq::from_raw([
            0x670b_cf6f_8b48_5dcd,
            0x8f3b_d43f_9926_0621,
            0x4a86_9553_c9d0_07f8,
            0x153e_e614_2e53_5e33,
        ]),
        Fq::from_raw([
            0xd258_d2e2_b778_2172,
            0x968a_d442_4af8_3700,
            0x635e_f7e7_a430_b486,
            0x0c45_bfd3_a69a_aa65,
        ]),
        Fq::from_raw([
            0x0e56_33d2_51f7_3307,
            0x6897_ac0a_8ffa_5ff1,
            0xf2d5_6aec_8314_4600,
            0x0adf_d53b_256a_6957,
        ]),
    ],
    [
        Fq::from_raw([
            0xac9d_36a8_b751_6d63,
            0x3f87_b28f_1c1b_e4bd,
            0x8cd1_726b_7cba_b8ee,
            0x315d_2ac8_ebdb_ac3c,
        ]),
        Fq::from_raw([
            0x299c_e44e_a423_d8e1,
            0xc9bb_60d1_f695_9879,
            0xcfae_c23d_2b16_883f,
            0x1b84_7271_2d02_eef4,
        ]),
        Fq::from_raw([
            0xc4a5_4041_98ad_f70c,
            0x367d_2c54_e369_28c9,
            0xbd0b_70fa_2255_eb6f,
            0x3c1c_d07e_fda6_ff24,
        ]),
    ],
    [
        Fq::from_raw([
            0xbbe5_23ae_f9ab_107a,
            0x4a16_073f_738f_7e0c,
            0x687f_4e51_b2e1_dcd3,
            0x1360_52d2_6bb3_d373,
        ]),
        Fq::from_raw([
            0x676c_36c2_4ef9_67dd,
            0x7b3c_fbb8_7303_2681,
            0xc1bd_d859_a123_2a1d,
            0x16c9_6bee_f6a0_a848,
        ]),
        Fq::from_raw([
            0x067e_ec7f_2d63_40c4,
            0x0123_87ba_b4f1_662d,
            0x2ab7_fed8_f499_a9fb,
            0x284b_38c5_7ff6_5c26,
        ]),
    ],
    [
        Fq::from_raw([
            0xaf1d_ff20_4c92_2f86,
            0xfc06_772c_1c04_11a6,
            0x39e2_4219_8897_d17c,
            0x0c59_93d1_75e8_1f66,
        ]),
        Fq::from_raw([
            0xbbf5_3f67_b1f8_7b15,
            0xf248_87ad_48e1_7759,
            0xfcda_655d_1ba9_c8f9,
            0x03bf_7a3f_7bd0_43da,
        ]),
        Fq::from_raw([
            0x9b5c_d09e_36d8_be62,
            0x4c8f_9cbe_69f0_e827,
            0xb0cf_9995_67f0_0e73,
            0x3188_fe4e_e9f9_fafb,
        ]),
    ],
    [
        Fq::from_raw([
            0xafea_99a2_ec6c_595a,
            0x3af5_bf77_c1c4_2652,
            0x5a39_768c_480d_61e1,
            0x171f_528c_cf65_8437,
        ]),
        Fq::from_raw([
            0x5a05_63b9_b8e9_f1d5,
            0x812c_3286_ee70_0067,
            0x196e_4185_9b35_ef88,
            0x12f4_175c_4ab4_5afc,
        ]),
        Fq::from_raw([
            0x0e74_d4d3_6911_8b79,
            0x7e23_e1aa_be96_cfab,
            0x8f8f_dcf8_00a9_ac69,
            0x3a50_9e15_5cb7_ebfd,
        ]),
    ],
    [
        Fq::from_raw([
            0x9871_2c65_678c_fd30,
            0x984b_c8f2_e4c1_b69e,
            0x1a89_920e_2504_c3b3,
            0x10f2_a685_df4a_27c8,
        ]),
        Fq::from_raw([
            0xe8a1_6728_cc9d_4918,
            0x5457_3c93_33c5_6321,
            0x1d8d_93d5_4ab9_1a0e,
            0x09e5_f497_90c8_a0e2,
        ]),
        Fq::from_raw([
            0x609a_7403_47cf_5fea,
            0x42d1_7ed6_ee0f_ab7e,
            0x2bf3_5705_d9f8_4a34,
            0x352d_69be_d80e_e3e5,
        ]),
    ],
    [
        Fq::from_raw([
            0x3a75_8af6_fa84_e0e8,
            0xc634_debd_281b_76a6,
            0x4915_62fa_f2b1_90d3,
            0x058e_e73b_a9f3_f293,
        ]),
        Fq::from_raw([
            0x621a_1325_10a4_3904,
            0x092c_b921_19bc_76be,
            0xcd0f_1fc5_5b1a_3250,
            0x232f_99cc_911e_ddd9,
        ]),
        Fq::from_raw([
            0xc3b9_7c1e_301b_c213,
            0xf9ef_d52c_a6bc_2961,
            0x86c2_2c6c_5d48_69f0,
            0x201b_eed7_b8f3_ab81,
        ]),
    ],
    [
        Fq::from_raw([
            0xbf6b_3431_ba94_e9bc,
            0x2938_8842_744a_1210,
            0xa1c9_291d_5860_2f51,
            0x1376_dce6_5800_30c6,
        ]),
        Fq::from_raw([
            0x6454_843c_5486_d7b3,
            0x072b_a8b0_2d92_e722,
            0x2b33_56c3_8238_f761,
            0x1793_199e_6fd6_ba34,
        ]),
        Fq::from_raw([
            0x06a3_f1d3_b433_311b,
            0x3c66_160d_c62a_acac,
            0x9fee_9c20_c87a_67df,
            0x22de_7a74_88dc_c735,
        ]),
    ],
    [
        Fq::from_raw([
            0x30d6_e3fd_516b_47a8,
            0xdbe0_b77f_ae77_e1d0,
            0xdf8f_f37f_e2d8_edf8,
            0x3514_d5e9_066b_b160,
        ]),
        Fq::from_raw([
            0x1937_7427_137a_81c7,
            0xff45_3d6f_900f_144a,
            0xf919_a00d_abbf_5fa5,
            0x30cd_3006_931a_d636,
        ]),
        Fq::from_raw([
            0x5b6a_7422_0692_b506,
            0x8f9e_4b2c_ae2e_bb51,
            0x41f8_1a5c_f613_c8df,
            0x253d_1a5c_5293_4127,
        ]),
    ],
    [
        Fq::from_raw([
            0x73f6_66cb_86a4_8e8e,
            0x851b_3a59_c990_fafc,
            0xa35e_9613_e7f5_fe92,
            0x035b_461c_02d7_9d19,
        ]),
        Fq::from_raw([
            0x7cfb_f86a_3aa0_4780,
            0x92b1_283c_2d5f_ccde,
            0x5bc0_0eed_d56b_93e0,
            0x23a9_9280_79d1_75bd,
        ]),
        Fq::from_raw([
            0xf1e4_ccd7_3fa0_0a82,
            0xb5e2_ea34_36ee_f957,
            0xf159_4a07_63c6_11ab,
            0x13a7_785a_e134_ea92,
        ]),
    ],
    [
        Fq::from_raw([
            0xbbf0_4f52_52de_4279,
            0x3889_c578_6344_6d88,
            0x4962_ae3c_0da1_7e31,
            0x39fc_e308_b7d4_3c57,
        ]),
        Fq::from_raw([
            0x3b57_e344_89b5_3fad,
            0xbef0_0a08_c6ed_38d2,
            0xc0fd_f016_62f6_0d22,
            0x1aae_1883_3f8e_1d3a,
        ]),
        Fq::from_raw([
            0x5551_3e03_3398_513f,
            0x27c1_b3fd_8f85_d8a8,
            0x8b2e_80c0_64fd_83ed,
            0x1a76_1ce8_2400_af01,
        ]),
    ],
    [
        Fq::from_raw([
            0x5244_ca74_9b73_e481,
            0xdcf6_af28_30a5_0287,
            0x16dd_1a87_ca22_e1cc,
            0x275a_03e4_5add_a7c3,
        ]),
        Fq::from_raw([
            0x58a2_53cf_b6a9_5786,
            0x07e5_6145_3fc5_648b,
            0xeb08_e47e_5fea_bcf8,
            0x2e5a_10f0_8b5a_b8bb,
        ]),
        Fq::from_raw([
            0xe033_d82c_efe7_8ce3,
            0xc141_a5b6_d594_bec4,
            0xb84e_9c33_3b29_32f1,
            0x1459_cb85_8720_8473,
        ]),
    ],
    [
        Fq::from_raw([
            0x5cec_7e7b_338f_be1b,
            0x52f9_332f_bffc_fbbd,
            0x7b92_ce81_0e14_a400,
            0x193a_e592_1d78_b5de,
        ]),
        Fq::from_raw([
            0x6022_4be6_7248_e82c,
            0x3743_84f4_a072_8205,
            0x8911_1fb2_c466_0281,
            0x3097_898a_5d00_11a4,
        ]),
        Fq::from_raw([
            0x5499_80de_8629_30f5,
            0x1979_b2d1_c465_b4d9,
            0x5717_82fd_96ce_54b4,
            0x378d_97bf_8c86_4ae7,
        ]),
    ],
    [
        Fq::from_raw([
            0x37ea_32a9_71d1_7884,
            0xdbc7_f5cb_4609_3421,
            0x8813_6287_ce37_6b08,
            0x2eb0_4ea7_c01d_97ec,
        ]),
        Fq::from_raw([
            0xead3_726f_1af2_e7b0,
            0x861c_bda4_7680_4e6c,
            0x2302_a1c2_2e49_baec,
            0x3642_5347_ea03_f641,
        ]),
        Fq::from_raw([
            0xecd6_27e5_9590_d09e,
            0x3f5b_5ca5_a19a_9701,
            0xcc99_6cd8_5c98_a1d8,
            0x26b7_2df4_7408_ad42,
        ]),
    ],
    [
        Fq::from_raw([
            0x59be_ce31_f0a3_1e95,
            0xde01_212e_e458_8f89,
            0x1f05_636c_610b_89aa,
            0x1301_80e4_4e29_24db,
        ]),
        Fq::from_raw([
            0x9ea8_e7bc_7926_3550,
            0xdf77_93cc_89e5_b52f,
            0x7327_5aca_ed5f_579c,
            0x219e_9773_7d39_79ba,
        ]),
        Fq::from_raw([
            0x9c12_635d_f251_d153,
            0x3b06_72dd_7d42_cbb4,
            0x3461_363f_81c4_89a2,
            0x3cdb_9359_8a5c_a528,
        ]),
    ],
    [
        Fq::from_raw([
            0x2861_ce16_f219_d5a9,
            0x4ad0_4470_45a7_c5aa,
            0x2072_4b92_7a0c_a81c,
            0x0e59_e6f3_32d7_ed37,
        ]),
        Fq::from_raw([
            0x43b0_a3fc_ff20_36bd,
            0x172c_c07b_9d33_fbf9,
            0x3d73_6946_7222_697a,
            0x1b06_4342_d51a_4275,
        ]),
        Fq::from_raw([
            0x3eb3_1022_8a0e_5f6c,
            0x78fa_9fb9_1712_21b7,
            0x2f36_3c55_b288_2e0b,
            0x30b8_2a99_8cbd_8e8a,
        ]),
    ],
    [
        Fq::from_raw([
            0xe46f_6d42_9874_0107,
            0x8ad7_1ea7_15be_0573,
            0x63df_7a76_e858_a4aa,
            0x23e4_ab37_183a_cba4,
        ]),
        Fq::from_raw([
            0xfca9_95e2_b599_14a1,
            0xacfe_1464_0de0_44f2,
            0x5d33_094e_0bed_a75b,
            0x2795_d5c5_fa42_8022,
        ]),
        Fq::from_raw([
            0xc26d_909d_ee8b_53c0,
            0xa668_7c3d_f16c_8fe4,
            0xd765_f26d_d03f_4c45,
            0x3001_ca40_1e89_601c,
        ]),
    ],
    [
        Fq::from_raw([
            0xe7fe_a6bd_f347_1380,
            0xe84b_5beb_ae4e_501d,
            0xf7bf_86e8_9280_827f,
            0x0072_e45c_c676_b08e,
        ]),
        Fq::from_raw([
            0xd0c5_4dde_b26b_86c0,
            0xb648_29e2_d40e_41bd,
            0xe2ab_e4c5_18ce_599e,
            0x13de_7054_8487_4bb5,
        ]),
        Fq::from_raw([
            0x3891_5b43_2a99_59a5,
            0x82bb_18e5_af1b_05bb,
            0x3159_50f1_211d_efe8,
            0x0408_a9fc_f9d6_1abf,
        ]),
    ],
    [
        Fq::from_raw([
            0x3407_0cbe_e268_86a0,
            0xae4d_23b0_b41b_e9a8,
            0xbb4e_4a14_00cc_d2c4,
            0x2780_b9e7_5b55_676e,
        ]),
        Fq::from_raw([
            0x9405_5920_98b4_056f,
            0xdc4d_8fbe_fe24_405a,
            0xf803_33ec_8563_4ac9,
            0x3a57_0d4d_7c4e_7ac3,
        ]),
        Fq::from_raw([
            0x78d2_b247_8995_20b4,
            0xe2cc_1507_bebd_cc62,
            0xf347_c247_fcf0_9294,
            0x0c13_cca7_cb1f_9d2c,
        ]),
    ],
    [
        Fq::from_raw([
            0x2e8c_88f7_7074_70e0,
            0x0b50_bb2e_b82d_f74d,
            0xd261_4a19_7c6b_794b,
            0x14f5_9baa_03cd_0ca4,
        ]),
        Fq::from_raw([
            0xbe52_476e_0a16_f3be,
            0xa51d_54ed_e661_67f5,
            0x6f54_6e17_04c3_9c60,
            0x307d_efee_925d_fb43,
        ]),
        Fq::from_raw([
            0x380b_67d8_0473_dce3,
            0x6611_0683_6adf_e5e7,
            0x7a07_e767_4b5a_2621,
            0x1960_cd51_1a91_e060,
        ]),
    ],
    [
        Fq::from_raw([
            0x15aa_f1f7_7125_89dd,
            0xb8ee_335d_8828_4cbe,
            0xca2a_d0fb_5667_2500,
            0x2301_ef9c_63ea_84c5,
        ]),
        Fq::from_raw([
            0x5e68_478c_4d60_27a9,
            0xc861_82d1_b424_6b58,
            0xd10f_4cd5_2be9_7f6b,
            0x029a_5a47_da79_a488,
        ]),
        Fq::from_raw([
            0x2cc4_f962_eaae_2260,
            0xf97f_e46b_6a92_5428,
            0x2360_d17d_890e_55cb,
            0x32d7_b16a_7f11_cc96,
        ]),
    ],
    [
        Fq::from_raw([
            0xc0ca_b915_d536_3d9f,
            0xa5f2_404c_d7b3_5eb0,
            0x18e8_57a9_8d49_8cf7,
            0x2670_3e48_c03b_81ca,
        ]),
        Fq::from_raw([
            0xf691_123a_e112_b928,
            0xf443_88bd_6b89_221e,
            0x88ac_8d25_a246_03f1,
            0x0486_82a3_5b32_65bc,
        ]),
        Fq::from_raw([
            0x3ab7_defc_b8d8_03e2,
            0x91d6_e171_5164_775e,
            0xd72c_ddc6_cf06_b507,
            0x06b1_3904_41fa_7030,
        ]),
    ],
    [
        Fq::from_raw([
            0xbcd7_9541_4a6e_2e86,
            0x43b3_60f6_386a_86d7,
            0x1689_426d_ce05_fcd8,
            0x31aa_0eeb_868c_626d,
        ]),
        Fq::from_raw([
            0xed77_f5d5_76b9_9cc3,
            0x90ef_d8f4_1b20_78b2,
            0x057a_bad3_764c_104b,
            0x2394_64f7_5bf7_b6af,
        ]),
        Fq::from_raw([
            0xb2cb_4873_07c1_cecf,
            0xa5cc_47c5_9654_b2a7,
            0xa45e_19ed_813a_54ab,
            0x0a64_d4c0_4fd4_26bd,
        ]),
    ],
    [
        Fq::from_raw([
            0x1f73_1532_2f65_8735,
            0x777c_7a92_1a06_2e9d,
            0x576a_4ad2_5986_0fb1,
            0x21fb_bdbb_7367_0734,
        ]),
        Fq::from_raw([
            0x6743_2400_3fc5_2146,
            0x5b86_d294_63d3_1564,
            0xd937_1ca2_eb95_acf3,
            0x31b8_6f3c_f017_05d4,
        ]),
        Fq::from_raw([
            0x7045_f48a_a4eb_4f6f,
            0x1354_1d65_157e_e1ce,
            0x05ef_1736_d090_56f6,
            0x2bfd_e533_5437_7c91,
        ]),
    ],
    [
        Fq::from_raw([
            0x5a13_a58d_2001_1e2f,
            0xf4d5_239c_11d0_eafa,
            0xd558_f36e_65f8_eca7,
            0x1233_ca93_6ec2_4671,
        ]),
        Fq::from_raw([
            0x6e70_af0a_7a92_4b3a,
            0x8780_58d0_234a_576f,
            0xc437_846d_8e0b_2b30,
            0x27d4_52a4_3ac7_dea2,
        ]),
        Fq::from_raw([
            0xa025_76b9_4392_f980,
            0x6a30_641a_1c3d_87b2,
            0xe816_ea8d_a493_e0fa,
            0x2699_dba8_2184_e413,
        ]),
    ],
    [
        Fq::from_raw([
            0x608c_6f7a_61b5_6e55,
            0xf185_8466_4f8c_ab49,
            0xc398_8bae_e42e_4b10,
            0x36c7_22f0_efcc_8803,
        ]),
        Fq::from_raw([
            0x6e49_ac17_0dbb_7fcd,
            0x85c3_8899_a7b5_a833,
            0x08b0_f2ec_89cc_aa37,
            0x02b3_ff48_861e_339b,
        ]),
        Fq::from_raw([
            0xa8c5_ae03_ad98_e405,
            0x6fc3_ff4c_49eb_59ad,
            0x6016_2f44_27bc_657b,
            0x0b70_d061_d58d_8a7f,
        ]),
    ],
    [
        Fq::from_raw([
            0x2e06_cc4a_f33b_0a06,
            0xad3d_e8be_46ed_9693,
            0xf875_3ade_b9d7_cee2,
            0x3fc2_a13f_127f_96a4,
        ]),
        Fq::from_raw([
            0xc120_80ac_117e_e15f,
            0x00cb_3d62_1e17_1d80,
            0x1bd6_3434_ac8c_419f,
            0x0c41_a6e4_8dd2_3a51,
        ]),
        Fq::from_raw([
            0x9685_213e_9692_f5e1,
            0x72aa_ad7e_4e75_339d,
            0xed44_7653_7169_084e,
            0x2de8_072a_6bd8_6884,
        ]),
    ],
    [
        Fq::from_raw([
            0x0ad0_1184_567b_027c,
            0xb81c_f735_cc9c_39c0,
            0x9d34_96a3_d9fe_05ec,
            0x0355_7a8f_7b38_a17f,
        ]),
        Fq::from_raw([
            0x45bc_b5ac_0082_6abc,
            0x060f_4336_3d81_8e54,
            0xee97_6d34_282f_1a37,
            0x0b5f_5955_2f49_8735,
        ]),
        Fq::from_raw([
            0x2f29_09e1_7e22_b0df,
            0xf5d6_46e5_7507_e548,
            0xfedb_b185_70dc_7300,
            0x0e29_23a5_fee7_b878,
        ]),
    ],
    [
        Fq::from_raw([
            0xf71e_ed73_f15b_3326,
            0xcf1c_b37c_3b03_2af6,
            0xc787_be97_020a_7fdd,
            0x1d78_5005_a7a0_0592,
        ]),
        Fq::from_raw([
            0x0acf_bfb2_23f8_f00d,
            0xa590_b88a_3b06_0294,
            0x0ba5_fedc_b8f2_5bd2,
            0x1ad7_72c2_73d9_c6df,
        ]),
        Fq::from_raw([
            0xc1ce_13d6_0f2f_5031,
            0x8105_10eb_61f0_672d,
            0xa78f_3275_c278_234b,
            0x027b_d647_85fc_bd2a,
        ]),
    ],
    [
        Fq::from_raw([
            0x8337_f5e0_7923_a853,
            0xe224_3134_6945_7b8e,
            0xce6f_8ffe_a103_1b6d,
            0x2080_0f44_1b4a_0526,
        ]),
        Fq::from_raw([
            0xa33d_7bed_89a4_408a,
            0x36cd_c8ee_d662_ad37,
            0x6eea_2cd4_9f43_12b4,
            0x3d5a_d61d_7b65_f938,
        ]),
        Fq::from_raw([
            0x3bbb_ae94_cc19_5284,
            0x1df9_6cc0_3ea4_b26d,
            0x02c5_f91b_e4dd_8e3d,
            0x1333_8bc3_51fc_46dd,
        ]),
    ],
    [
        Fq::from_raw([
            0xc527_1c29_7852_819e,
            0x646c_49f9_b46c_bf19,
            0xb87d_b1e2_af3e_a923,
            0x25e5_2be5_07c9_2760,
        ]),
        Fq::from_raw([
            0x5c38_0ab7_01b5_2ea9,
            0xa34c_83a3_485c_6b2d,
            0x7109_6d8b_1b98_3c98,
            0x1c49_2d64_c157_aaa4,
        ]),
        Fq::from_raw([
            0xa20c_0b3d_a0da_4ca3,
            0xd434_87bc_288d_f682,
            0xf4e6_c5e7_a573_f592,
            0x0c5b_8015_7999_2718,
        ]),
    ],
    [
        Fq::from_raw([
            0x7ea3_3c93_e408_33cf,
            0x584e_9e62_a7f9_554e,
            0x6869_5c0c_d7cb_f43d,
            0x1090_b1b4_d2be_be7a,
        ]),
        Fq::from_raw([
            0xe383_e1ec_3baa_8d69,
            0x1b21_8e35_ecf2_328e,
            0x68f5_ce5c_bed1_9cad,
            0x33e3_8018_a801_387a,
        ]),
        Fq::from_raw([
            0xb76b_0b3d_787e_e953,
            0x5f4a_02d2_8729_e3ae,
            0xeef8_d83d_0e87_6bac,
            0x1654_af18_772b_2da5,
        ]),
    ],
    [
        Fq::from_raw([
            0xef7c_e6a0_1326_5477,
            0xbb08_9387_0367_ec6c,
            0x4474_2de8_8c5a_b0d5,
            0x1678_be3c_c9c6_7993,
        ]),
        Fq::from_raw([
            0xaf5d_4789_3348_f766,
            0xdaf1_8183_55b1_3b4f,
            0x7ff9_c6be_546e_928a,
            0x3780_bd1e_01f3_4c22,
        ]),
        Fq::from_raw([
            0xa123_8032_0d7c_c1de,
            0x5d11_e69a_a6c0_b98c,
            0x0786_018e_7cb7_7267,
            0x1e83_d631_5c9f_125b,
        ]),
    ],
    [
        Fq::from_raw([
            0x1799_603e_855c_e731,
            0xc486_894d_76e0_c33b,
            0x160b_4155_2f29_31c8,
            0x354a_fd0a_2f9d_0b26,
        ]),
        Fq::from_raw([
            0x8b99_7ee0_6be1_bff3,
            0x60b0_0dbe_1fac_ed07,
            0x2d8a_ffa6_2905_c5a5,
            0x00cd_6d29_f166_eadc,
        ]),
        Fq::from_raw([
            0x08d0_6419_1708_2f2c,
            0xc60d_0197_3f18_3057,
            0xdbe0_e3d7_cdbc_66ef,
            0x1d62_1935_2768_e3ae,
        ]),
    ],
    [
        Fq::from_raw([
            0xfa08_dd98_0638_7577,
            0xafe3_ca1d_b8d4_f529,
            0xe48d_2370_d7d1_a142,
            0x1463_36e2_5db5_181d,
        ]),
        Fq::from_raw([
            0xa901_d3ce_84de_0ad4,
            0x022e_54b4_9c13_d907,
            0x997a_2116_3e2e_43df,
            0x0005_d8e0_85fd_72ee,
        ]),
        Fq::from_raw([
            0x1c36_f313_4196_4484,
            0x6f8e_bc1d_2296_021a,
            0x0dd5_e61c_8a4e_8642,
            0x364e_97c7_a389_3227,
        ]),
    ],
    [
        Fq::from_raw([
            0xd7a0_0c03_d2e0_baaa,
            0xfa97_ec80_ad30_7a52,
            0x561c_6fff_1534_6878,
            0x0118_9910_671b_c16b,
        ]),
        Fq::from_raw([
            0x63fd_8ac5_7a95_ca8c,
            0x4c0f_7e00_1df4_90aa,
            0x5229_dfaa_0123_1a45,
            0x162a_7c80_f4d2_d12e,
        ]),
        Fq::from_raw([
            0x32e6_9efb_22f4_0b96,
            0xcaff_31b4_fda3_2124,
            0x2604_e4af_b09f_8603,
            0x2a0d_6c09_5766_66bb,
        ]),
    ],
    [
        Fq::from_raw([
            0xc0a0_180f_8cbf_c0d2,
            0xf444_d10d_63a7_4e2c,
            0xe16a_4d60_3d5a_808e,
            0x0978_e5c5_1e1e_5649,
        ]),
        Fq::from_raw([
            0x03f4_460e_bc35_1b6e,
            0x0508_7d90_3bda_cfd1,
            0xebe1_9bbd_ce25_1011,
            0x1bdc_ee3a_aca9_cd25,
        ]),
        Fq::from_raw([
            0xf619_64bf_3ade_7670,
            0x0c94_7321_e007_5e3f,
            0xe494_7914_0b19_44fd,
            0x1862_cccb_70b5_b885,
        ]),
    ],
    [
        Fq::from_raw([
            0xc326_7da6_e94a_dc50,
            0x39ee_99c1_cc6e_5dda,
            0xbc26_cc88_3a19_87e1,
            0x1f3e_91d8_63c1_6922,
        ]),
        Fq::from_raw([
            0x0f85_b4ac_2c36_7406,
            0xfa66_1465_c656_ad99,
            0xef5c_08f8_478f_663a,
            0x1af4_7a48_a601_6a49,
        ]),
        Fq::from_raw([
            0x0eab_cd87_e7d0_1b15,
            0x1c36_98b0_a2e3_da10,
            0x009d_5733_8c69_3505,
            0x3c8e_e901_956e_3d3f,
        ]),
    ],
    [
        Fq::from_raw([
            0x8b94_7721_8967_3476,
            0xe10c_e2b7_069f_4dbd,
            0x68d0_b024_f591_b520,
            0x1660_a8cd_e7fe_c553,
        ]),
        Fq::from_raw([
            0x9d8d_0f67_fdaa_79d5,
            0x3963_c2c1_f558_6e2f,
            0x1303_9363_34dd_1132,
            0x0f6d_9919_29d5_e4e7,
        ]),
        Fq::from_raw([
            0x7a43_3091_e1ce_2d3a,
            0x4e7f_da77_0712_f343,
            0xcc62_5eaa_ab52_b4dc,
            0x02b9_cea1_921c_d9f6,
        ]),
    ],
    [
        Fq::from_raw([
            0x3797_b2d8_3760_43b3,
            0xd8ca_f468_976f_0472,
            0x214f_7c67_84ac_b565,
            0x14a3_23b9_9b90_0331,
        ]),
        Fq::from_raw([
            0x347f_ef2c_00f0_953a,
            0x718b_7fbc_7788_af78,
            0xec01_ea79_642d_5760,
            0x1904_76b5_80cb_9277,
        ]),
        Fq::from_raw([
            0xff4e_7e6f_b268_dfd7,
            0x9660_902b_6008_7651,
            0xa424_63d3_0b44_2b6f,
            0x090a_3a9d_869d_2eef,
        ]),
    ],
    [
        Fq::from_raw([
            0xf983_387e_a045_6203,
            0xe365_0013_04f9_a11e,
            0x0dbe_8fd2_270a_6795,
            0x3877_a955_8636_7567,
        ]),
        Fq::from_raw([
            0x39c0_af0f_e01f_4a06,
            0x6011_8c53_a218_1352,
            0x5df3_9a2c_c63d_dc0a,
            0x2d89_4691_240f_e953,
        ]),
        Fq::from_raw([
            0x1aca_9eaf_9bba_9850,
            0x5914_e855_eeb4_4aa1,
            0x7ef7_1780_2016_6189,
            0x21b9_c182_92bd_bc59,
        ]),
    ],
    [
        Fq::from_raw([
            0x33f5_09a7_4ad9_d39b,
            0x272e_1cc6_c36a_2968,
            0x505a_05f2_a6ae_834c,
            0x2fe7_6be7_cff7_23e2,
        ]),
        Fq::from_raw([
            0x0df9_fa97_277f_a8b4,
            0xd15b_ff84_0dda_e8a5,
            0x9299_81d7_cfce_253b,
            0x187a_a448_f391_e3ca,
        ]),
        Fq::from_raw([
            0xf0c6_6af5_ffc7_3736,
            0x663c_cf7b_2ffe_4b5e,
            0x007a_b3aa_3617_f422,
            0x0b70_83ad_7517_07bf,
        ]),
    ],
    [
        Fq::from_raw([
            0x2f9b_20f1_fbd4_9791,
            0x1975_b962_f6cb_8e0b,
            0x3bc4_ca99_02c5_2acb,
            0x030d_dbb4_7049_3f16,
        ]),
        Fq::from_raw([
            0x3a1c_62ca_8fbf_2525,
            0x8fb8_ab9d_60ea_17b2,
            0x950b_0ab1_8d35_46df,
            0x3130_fbaf_fb5a_a82a,
        ]),
        Fq::from_raw([
            0x43a8_7618_0dc3_82e0,
            0x15ce_2ead_2fcd_051e,
            0x4f74_d74b_ac2e_e457,
            0x337f_5447_07c4_30f0,
        ]),
    ],
    [
        Fq::from_raw([
            0x26de_98a8_736d_1d11,
            0x7d8e_471a_9fb9_5fef,
            0xac9d_91b0_930d_ac75,
            0x3499_7991_9015_394f,
        ]),
        Fq::from_raw([
            0xccfc_b618_31d5_c775,
            0x3bf9_3da6_fff3_1d95,
            0x2305_cd7a_921e_c5f1,
            0x027c_c4ef_e3fb_35dd,
        ]),
        Fq::from_raw([
            0xc3fa_2629_635d_27de,
            0x67f1_c6b7_3147_64af,
            0x61b7_1a36_9868_2ad2,
            0x037f_9f23_6595_4c5b,
        ]),
    ],
    [
        Fq::from_raw([
            0x77c5_b024_8483_71ae,
            0x6041_4abe_362d_01c9,
            0x10f1_cc6d_f8b4_bcd7,
            0x1f69_7cac_4d07_feb7,
        ]),
        Fq::from_raw([
            0x786a_dd24_4aa0_ef29,
            0x3145_c478_0631_09d6,
            0x26e6_c851_fbd5_72a6,
            0x267a_750f_e5d7_cfbc,
        ]),
        Fq::from_raw([
            0x180e_2b4d_3e75_6f65,
            0xaf28_5fa8_2ce4_fae5,
            0x678c_9996_d9a4_72c8,
            0x0c91_feab_4a43_193a,
        ]),
    ],
    [
        Fq::from_raw([
            0x79c4_7c57_3ac4_10f7,
            0x7e3b_83af_4a4b_a3ba,
            0x2186_c303_8ea0_5e69,
            0x1745_569a_0a3e_3014,
        ]),
        Fq::from_raw([
            0x1e03_8852_2696_191f,
            0xfdff_66c6_f3b5_ffe1,
            0xeca5_1207_78a5_6711,
            0x2986_3d54_6e7e_7c0d,
        ]),
        Fq::from_raw([
            0x2f22_5e63_66bf_e390,
            0xa79a_03df_8339_94c6,
            0xbf06_bae4_9ef8_53f6,
            0x1148_d6ab_2bd0_0192,
        ]),
    ],
    [
        Fq::from_raw([
            0xf4f6_331a_8b26_5d15,
            0xf745_f45d_350d_41d4,
            0xe18b_1499_060d_a366,
            0x02e0_e121_b0f3_dfef,
        ]),
        Fq::from_raw([
            0x078a_e6aa_1510_54b7,
            0x6904_0173_6d44_a653,
            0xb89e_f73a_40a2_b274,
            0x0d0a_a46e_76a6_a278,
        ]),
        Fq::from_raw([
            0x9a4d_532c_7b6e_0958,
            0x392d_de71_0f1f_06db,
            0xeee5_45f3_fa6d_3d08,
            0x1394_3675_b04a_a986,
        ]),
    ],
    [
        Fq::from_raw([
            0x961f_c818_dcbb_66b5,
            0xc9f2_b325_7530_dafe,
            0xd97a_11d6_3088_f5d9,
            0x2901_ec61_942d_34aa,
        ]),
        Fq::from_raw([
            0xfdf5_44b9_63d1_fdc7,
            0x22ff_a2a2_af9f_a3e3,
            0xf431_d544_34a3_e0cf,
            0x2020_4a21_05d2_2e7e,
        ]),
        Fq::from_raw([
            0x1211_b9e2_190d_6852,
            0xa004_abe8_e015_28c4,
            0x5c1e_3e9e_27a5_71c3,
            0x3a8a_6282_9512_1d5c,
        ]),
    ],
];

// n: 255
// t: 3
// N: 765
// Result Algorithm 1:
//  [True, 0]
// Result Algorithm 2:
//  [True, None]
// Result Algorithm 3:
//  [True, None]
// Prime number: 0x0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

pub(crate) const MDS: [[Fq; 3]; 3] = [
    [
        Fq::from_raw([
            0xeb4f_1f74_2963_421f,
            0x5f71_0afc_43dd_c5f6,
            0x9191_3f56_cf21_af2b,
            0x1853_b497_7c6f_a227,
        ]),
        Fq::from_raw([
            0x45e5_1db6_ac6f_e4a7,
            0x5a0f_a4df_a500_bcad,
            0x63f4_84c1_0fcf_0586,
            0x3d83_1189_cfbb_c452,
        ]),
        Fq::from_raw([
            0xd188_37f9_8347_f137,
            0x3f89_65c7_8083_8a94,
            0x4ba8_8b9e_4017_19c0,
            0x3a0e_3f84_d3c1_77d8,
        ]),
    ],
    [
        Fq::from_raw([
            0x84fd_7923_337c_f77e,
            0x2896_f8d0_fd5c_9a75,
            0x8e9d_c529_f471_8f83,
            0x35e2_6e39_8450_6279,
        ]),
        Fq::from_raw([
            0x3eb9_24f5_6fff_7908,
            0x3641_cecf_3a2a_5a8a,
            0x00cd_7dbe_a799_70ab,
            0x10a8_1663_02cb_753c,
        ]),
        Fq::from_raw([
            0xb672_27c1_a141_ae94,
            0x198e_1aee_777e_2521,
            0xf434_92ce_5121_4b00,
            0x314f_762a_506d_321b,
        ]),
    ],
    [
        Fq::from_raw([
            0xabcb_d614_eaf5_eba1,
            0xa90f_28b0_cb31_76fb,
            0xcb2e_ab86_ef31_d915,
            0x07b8_5627_c832_782a,
        ]),
        Fq::from_raw([
            0xc255_efd0_06b5_db1c,
            0xb5d9_85dc_1630_a4b2,
            0x9756_4e1b_5d1a_c72f,
            0x2a2d_e13e_70f2_7e16,
        ]),
        Fq::from_raw([
            0xcffd_f529_3334_29fc,
            0x21e3_af7e_f123_32cd,
            0xfff5_40a8_7327_c7ce,
            0x2c60_94d1_c6e1_caba,
        ]),
    ],
];

pub(crate) const MDS_INV: [[Fq; 3]; 3] = [
    [
        Fq::from_raw([
            0xb204_ddc6_5e58_2044,
            0x47a6_0484_b0a9_9c91,
            0xcaf5_4d78_24c1_200e,
            0x36df_4950_21cf_7828,
        ]),
        Fq::from_raw([
            0x6a6b_94ad_aa0d_9c9e,
            0xe2cd_38b9_59d4_61ff,
            0xe43e_c4bf_3e0d_f00c,
            0x034f_beae_4650_c2c7,
        ]),
        Fq::from_raw([
            0xa862_7a02_8c1a_f7d6,
            0x841b_ebf1_a15b_746e,
            0x1fd5_6832_d0ab_5570,
            0x20a8_64d6_790f_7c1c,
        ]),
    ],
    [
        Fq::from_raw([
            0x3470_d5c5_53bc_9d20,
            0x1f95_660f_eb5d_b121,
            0xdd31_97ac_c894_9076,
            0x2d08_703d_48ec_d7dc,
        ]),
        Fq::from_raw([
            0x6b5b_42b0_67d8_30f3,
            0x6169_b6fa_721a_470e,
            0xeff3_18a2_8983_158a,
            0x2db1_0ecd_507a_2f27,
        ]),
        Fq::from_raw([
            0xfbae_b537_d278_4760,
            0x0068_e709_07e7_089d,
            0x926a_5fc0_cc1e_f726,
            0x0c8a_58c0_6473_cdfa,
        ]),
    ],
    [
        Fq::from_raw([
            0x3a5a_ca10_7129_6e61,
            0x4ad4_442e_96c9_d5e8,
            0x5432_f0c0_b908_a411,
            0x2a64_2dca_695d_744d,
        ]),
        Fq::from_raw([
            0x1bd9_bfcb_be02_5ff1,
            0x24f6_ad43_b703_ad90,
            0xebb7_238d_f00d_17e7,
            0x114e_c796_fb40_3f5f,
        ]),
        Fq::from_raw([
            0x67f0_642e_14a9_c3bf,
            0xf6a6_9176_7069_7a97,
            0x0408_110d_c66e_b147,
            0x2825_e067_5968_dbeb,
        ]),
    ],
];
