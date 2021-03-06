// Copyright, 2021, Gé Vissers
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use babs::{UBigBin8, UBigDec8, UBigBin32, UBigDec32, UBigBin64, UBigDec64};
use std::str::FromStr;

#[test]
fn test_square_binary()
{
    let n = UBigBin8::from_str("0xaabbccddeeff00998877665544332211").unwrap();
    let nsq = n.square();
    assert_eq!(format!("{:#x}", nsq), "0x71ddf5dbb1984aa3b5e6d00c54005c14678e40e5e3a082ccd7135f999f4e8521");

    let n = UBigBin32::from_str("0x8782defe72928faed45543232223fd298743fdfe6282d35ef256ffff3282912ff").unwrap();
    let nsq = n.square();
    assert_eq!(format!("{:#x}", nsq), "0x47bb4a1799813c0210d0c678607db42588d651f6cec650ad64d352b37679c705a8e52595f01d20c894af36365da1d27f656f0580369a9412354740eea0c716da01");

    let n = UBigBin64::from_str("0x8782defe72928faed45543232223fd298743fdfe6282d35ef256ffff3282912ff").unwrap();
    let nsq = n.square();
    assert_eq!(format!("{:#x}", nsq), "0x47bb4a1799813c0210d0c678607db42588d651f6cec650ad64d352b37679c705a8e52595f01d20c894af36365da1d27f656f0580369a9412354740eea0c716da01");

    let n = UBigBin8::from_str("0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap();
    let nsq = n.square();
    assert_eq!(format!("{:#x}", nsq), "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000000000000000000000000000000000000000000001");

    let n = UBigBin64::from_str("0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap();
    let nsq = n.square();
    assert_eq!(format!("{:#x}", nsq), "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000000000000000000000000000000000000000000001");
}

#[test]
fn test_square_decimal()
{
    let n = UBigDec8::from_str("90727377009702372093809109273071309").unwrap();
    let nsq = n.square();
    assert_eq!(format!("{}", nsq), "8231456939060670541592732870350998958165109827496929456075301798973481");

    let n = UBigDec32::from_str("93930273848473992847564646555552735478998990939373836272").unwrap();
    let nsq = n.square();
    assert_eq!(format!("{}", nsq), "8822896345249317283051705810912339219361910538931465262594904474090285837738020601641946335849934832374262857984");

    let n = UBigDec64::from_str("3290847429837828822896345249317283051705810912339219361910538931465262594904474090285837738020601641946335849934832374262857984").unwrap();
    let nsq = n.square();
    assert_eq!(format!("{}", nsq), "10829676806470243697243025330900165325427709743339480433570580434846912014896850953531952081670526694872997116697146897578279823010880330068960918790299855167047725234049466035765365196628178125021675079324727934964042656069974880069014484242351752544256");

    let n = UBigDec8::from_str("999999999999999999999999999999999999999999999999999999999999999999999999999999999999").unwrap();
    let nsq = n.square();
    assert_eq!(format!("{}", nsq), "999999999999999999999999999999999999999999999999999999999999999999999999999999999998000000000000000000000000000000000000000000000000000000000000000000000000000000000001");

    let n = UBigDec64::from_str("999999999999999999999999999999999999999999999999999999999999999999999999999999999999").unwrap();
    let nsq = n.square();
    assert_eq!(format!("{}", nsq), "999999999999999999999999999999999999999999999999999999999999999999999999999999999998000000000000000000000000000000000000000000000000000000000000000000000000000000000001");
}
