module

public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Model

/-! Generated from the exact pinned T16 native frame catalog. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Geometry

def frame96 : Frame := ⟨1, ![41#9], ![1#9]⟩
theorem frame96_dual : frame96.DualCheck := by decide
def checkedFrame96 : CertifiedFrame := ⟨frame96, frame96.independent frame96_dual⟩

def frame97 : Frame := ⟨1, ![439#9], ![1#9]⟩
theorem frame97_dual : frame97.DualCheck := by decide
def checkedFrame97 : CertifiedFrame := ⟨frame97, frame97.independent frame97_dual⟩

def frame98 : Frame := ⟨1, ![388#9], ![4#9]⟩
theorem frame98_dual : frame98.DualCheck := by decide
def checkedFrame98 : CertifiedFrame := ⟨frame98, frame98.independent frame98_dual⟩

def frame99 : Frame := ⟨1, ![26#9], ![2#9]⟩
theorem frame99_dual : frame99.DualCheck := by decide
def checkedFrame99 : CertifiedFrame := ⟨frame99, frame99.independent frame99_dual⟩

def frame100 : Frame := ⟨1, ![463#9], ![1#9]⟩
theorem frame100_dual : frame100.DualCheck := by decide
def checkedFrame100 : CertifiedFrame := ⟨frame100, frame100.independent frame100_dual⟩

def frame101 : Frame := ⟨1, ![81#9], ![1#9]⟩
theorem frame101_dual : frame101.DualCheck := by decide
def checkedFrame101 : CertifiedFrame := ⟨frame101, frame101.independent frame101_dual⟩

def frame102 : Frame := ⟨1, ![98#9], ![2#9]⟩
theorem frame102_dual : frame102.DualCheck := by decide
def checkedFrame102 : CertifiedFrame := ⟨frame102, frame102.independent frame102_dual⟩

def frame103 : Frame := ⟨1, ![508#9], ![4#9]⟩
theorem frame103_dual : frame103.DualCheck := by decide
def checkedFrame103 : CertifiedFrame := ⟨frame103, frame103.independent frame103_dual⟩

def frame104 : Frame := ⟨2, ![41#9,26#9], ![1#9,2#9]⟩
theorem frame104_dual : frame104.DualCheck := by decide
def checkedFrame104 : CertifiedFrame := ⟨frame104, frame104.independent frame104_dual⟩

def frame105 : Frame := ⟨2, ![81#9,41#9], ![9#9,8#9]⟩
theorem frame105_dual : frame105.DualCheck := by decide
def checkedFrame105 : CertifiedFrame := ⟨frame105, frame105.independent frame105_dual⟩

def frame106 : Frame := ⟨2, ![75#9,41#9], ![2#9,3#9]⟩
theorem frame106_dual : frame106.DualCheck := by decide
def checkedFrame106 : CertifiedFrame := ⟨frame106, frame106.independent frame106_dual⟩

def frame107 : Frame := ⟨2, ![388#9,51#9], ![4#9,1#9]⟩
theorem frame107_dual : frame107.DualCheck := by decide
def checkedFrame107 : CertifiedFrame := ⟨frame107, frame107.independent frame107_dual⟩

def frame108 : Frame := ⟨2, ![439#9,120#9], ![1#9,8#9]⟩
theorem frame108_dual : frame108.DualCheck := by decide
def checkedFrame108 : CertifiedFrame := ⟨frame108, frame108.independent frame108_dual⟩

def frame109 : Frame := ⟨2, ![439#9,75#9], ![4#9,5#9]⟩
theorem frame109_dual : frame109.DualCheck := by decide
def checkedFrame109 : CertifiedFrame := ⟨frame109, frame109.independent frame109_dual⟩

def frame110 : Frame := ⟨2, ![388#9,75#9], ![4#9,1#9]⟩
theorem frame110_dual : frame110.DualCheck := by decide
def checkedFrame110 : CertifiedFrame := ⟨frame110, frame110.independent frame110_dual⟩

def frame111 : Frame := ⟨2, ![388#9,120#9], ![4#9,8#9]⟩
theorem frame111_dual : frame111.DualCheck := by decide
def checkedFrame111 : CertifiedFrame := ⟨frame111, frame111.independent frame111_dual⟩

def frame112 : Frame := ⟨2, ![75#9,26#9], ![1#9,3#9]⟩
theorem frame112_dual : frame112.DualCheck := by decide
def checkedFrame112 : CertifiedFrame := ⟨frame112, frame112.independent frame112_dual⟩

def frame113 : Frame := ⟨2, ![98#9,26#9], ![10#9,8#9]⟩
theorem frame113_dual : frame113.DualCheck := by decide
def checkedFrame113 : CertifiedFrame := ⟨frame113, frame113.independent frame113_dual⟩

def frame114 : Frame := ⟨2, ![463#9,51#9], ![4#9,5#9]⟩
theorem frame114_dual : frame114.DualCheck := by decide
def checkedFrame114 : CertifiedFrame := ⟨frame114, frame114.independent frame114_dual⟩

def frame115 : Frame := ⟨2, ![81#9,51#9], ![3#9,2#9]⟩
theorem frame115_dual : frame115.DualCheck := by decide
def checkedFrame115 : CertifiedFrame := ⟨frame115, frame115.independent frame115_dual⟩

def frame116 : Frame := ⟨3, ![388#9,98#9,26#9], ![4#9,10#9,8#9]⟩
theorem frame116_dual : frame116.DualCheck := by decide
def checkedFrame116 : CertifiedFrame := ⟨frame116, frame116.independent frame116_dual⟩

def frame117 : Frame := ⟨3, ![414#9,81#9,41#9], ![2#9,11#9,10#9]⟩
theorem frame117_dual : frame117.DualCheck := by decide
def checkedFrame117 : CertifiedFrame := ⟨frame117, frame117.independent frame117_dual⟩

def frame118 : Frame := ⟨3, ![429#9,75#9,26#9], ![4#9,5#9,7#9]⟩
theorem frame118_dual : frame118.DualCheck := by decide
def checkedFrame118 : CertifiedFrame := ⟨frame118, frame118.independent frame118_dual⟩

def frame119 : Frame := ⟨3, ![388#9,75#9,41#9], ![4#9,2#9,3#9]⟩
theorem frame119_dual : frame119.DualCheck := by decide
def checkedFrame119 : CertifiedFrame := ⟨frame119, frame119.independent frame119_dual⟩

def frame120 : Frame := ⟨3, ![388#9,75#9,26#9], ![4#9,1#9,3#9]⟩
theorem frame120_dual : frame120.DualCheck := by decide
def checkedFrame120 : CertifiedFrame := ⟨frame120, frame120.independent frame120_dual⟩

def frame121 : Frame := ⟨3, ![414#9,75#9,41#9], ![4#9,6#9,7#9]⟩
theorem frame121_dual : frame121.DualCheck := by decide
def checkedFrame121 : CertifiedFrame := ⟨frame121, frame121.independent frame121_dual⟩

def frame122 : Frame := ⟨3, ![429#9,98#9,26#9], ![1#9,11#9,9#9]⟩
theorem frame122_dual : frame122.DualCheck := by decide
def checkedFrame122 : CertifiedFrame := ⟨frame122, frame122.independent frame122_dual⟩

def frame123 : Frame := ⟨3, ![388#9,81#9,41#9], ![4#9,9#9,8#9]⟩
theorem frame123_dual : frame123.DualCheck := by decide
def checkedFrame123 : CertifiedFrame := ⟨frame123, frame123.independent frame123_dual⟩

def frame124 : Frame := ⟨4, ![388#9,75#9,41#9,26#9], ![4#9,11#9,10#9,9#9]⟩
theorem frame124_dual : frame124.DualCheck := by decide
def checkedFrame124 : CertifiedFrame := ⟨frame124, frame124.independent frame124_dual⟩

def frame125 : Frame := ⟨1, ![375#9], ![1#9]⟩
theorem frame125_dual : frame125.DualCheck := by decide
def checkedFrame125 : CertifiedFrame := ⟨frame125, frame125.independent frame125_dual⟩

def frame126 : Frame := ⟨1, ![196#9], ![4#9]⟩
theorem frame126_dual : frame126.DualCheck := by decide
def checkedFrame126 : CertifiedFrame := ⟨frame126, frame126.independent frame126_dual⟩

def frame127 : Frame := ⟨1, ![247#9], ![1#9]⟩
theorem frame127_dual : frame127.DualCheck := by decide
def checkedFrame127 : CertifiedFrame := ⟨frame127, frame127.independent frame127_dual⟩


end IntegerMultBounds.Networks.Certificates.T16.Geometry
