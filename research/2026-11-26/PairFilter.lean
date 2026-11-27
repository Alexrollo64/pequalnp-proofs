import Mathlib
namespace Alexrollo64.PairFilter
/- Six coordinates per block, ordered as rows 2,3,4 and columns 0,1,4.
The 48 cells iterate over row block, column block, local row (0,2,3,4)
and local column (0,1,4), in that order. A set bit of s is private to h.
The generator groups order comparisons with the same difference mask. -/
def costOK (s : BitVec 6) (v : BitVec 7) : Bool :=
  ((s.extractLsb' 0 1).zeroExtend 3 + (s.extractLsb' 1 1).zeroExtend 3 + (s.extractLsb' 2 1).zeroExtend 3 + (s.extractLsb' 3 1).zeroExtend 3 + (s.extractLsb' 4 1).zeroExtend 3 + (s.extractLsb' 5 1).zeroExtend 3 == (0 : BitVec 3) && ((0 : BitVec 128) >>> v).getLsbD 0) ||
  ((s.extractLsb' 0 1).zeroExtend 3 + (s.extractLsb' 1 1).zeroExtend 3 + (s.extractLsb' 2 1).zeroExtend 3 + (s.extractLsb' 3 1).zeroExtend 3 + (s.extractLsb' 4 1).zeroExtend 3 + (s.extractLsb' 5 1).zeroExtend 3 == (1 : BitVec 3) && ((5192296858539549995013640852475912 : BitVec 128) >>> v).getLsbD 0) ||
  ((s.extractLsb' 0 1).zeroExtend 3 + (s.extractLsb' 1 1).zeroExtend 3 + (s.extractLsb' 2 1).zeroExtend 3 + (s.extractLsb' 3 1).zeroExtend 3 + (s.extractLsb' 4 1).zeroExtend 3 + (s.extractLsb' 5 1).zeroExtend 3 == (2 : BitVec 3) && ((22982403970708864165704232180206108950 : BitVec 128) >>> v).getLsbD 0) ||
  ((s.extractLsb' 0 1).zeroExtend 3 + (s.extractLsb' 1 1).zeroExtend 3 + (s.extractLsb' 2 1).zeroExtend 3 + (s.extractLsb' 3 1).zeroExtend 3 + (s.extractLsb' 4 1).zeroExtend 3 + (s.extractLsb' 5 1).zeroExtend 3 == (3 : BitVec 3) && ((334792836512804912540943268658358643158 : BitVec 128) >>> v).getLsbD 0) ||
  ((s.extractLsb' 0 1).zeroExtend 3 + (s.extractLsb' 1 1).zeroExtend 3 + (s.extractLsb' 2 1).zeroExtend 3 + (s.extractLsb' 3 1).zeroExtend 3 + (s.extractLsb' 4 1).zeroExtend 3 + (s.extractLsb' 5 1).zeroExtend 3 == (4 : BitVec 3) && ((317294077068696447176673920497520766688 : BitVec 128) >>> v).getLsbD 0) ||
  ((s.extractLsb' 0 1).zeroExtend 3 + (s.extractLsb' 1 1).zeroExtend 3 + (s.extractLsb' 2 1).zeroExtend 3 + (s.extractLsb' 3 1).zeroExtend 3 + (s.extractLsb' 4 1).zeroExtend 3 + (s.extractLsb' 5 1).zeroExtend 3 == (5 : BitVec 3) && ((317294119060923387460670395419081338592 : BitVec 128) >>> v).getLsbD 0) ||
  ((s.extractLsb' 0 1).zeroExtend 3 + (s.extractLsb' 1 1).zeroExtend 3 + (s.extractLsb' 2 1).zeroExtend 3 + (s.extractLsb' 3 1).zeroExtend 3 + (s.extractLsb' 4 1).zeroExtend 3 + (s.extractLsb' 5 1).zeroExtend 3 == (6 : BitVec 3) && ((5484335575973810915689291762998969888 : BitVec 128) >>> v).getLsbD 0)

def insideOK0 (s : BitVec 12) (h : BitVec 48) : Bool :=
  (!h.getLsbD 0 || (((s &&& (8 : BitVec 12)) != 0 || (h &&& (281465162038710 : BitVec 48)) == (281465162038710 : BitVec 48)) && ((s &&& (0 : BitVec 12)) != 0 || (h &&& (9814671944 : BitVec 48)) == (9814671944 : BitVec 48)))) &&
  (!h.getLsbD 1 || (((s &&& (16 : BitVec 12)) != 0 || (h &&& (281455347366765 : BitVec 48)) == (281455347366765 : BitVec 48)) && ((s &&& (0 : BitVec 12)) != 0 || (h &&& (19629343888 : BitVec 48)) == (19629343888 : BitVec 48)))) &&
  (!h.getLsbD 2 || (((s &&& (32 : BitVec 12)) != 0 || (h &&& (281435718022875 : BitVec 48)) == (281435718022875 : BitVec 48)) && ((s &&& (0 : BitVec 12)) != 0 || (h &&& (39258687776 : BitVec 48)) == (39258687776 : BitVec 48)))) &&
  (!h.getLsbD 3 || (((s &&& (1 : BitVec 12)) != 0 || (h &&& (9814671937 : BitVec 48)) == (9814671937 : BitVec 48)) && ((s &&& (9 : BitVec 12)) != 0 || (h &&& (281465161809286 : BitVec 48)) == (281465161809286 : BitVec 48)) && ((s &&& (8 : BitVec 12)) != 0 || (h &&& (229424 : BitVec 48)) == (229424 : BitVec 48)))) &&
  (!h.getLsbD 4 || (((s &&& (17 : BitVec 12)) != 0 || (h &&& (281455347137349 : BitVec 48)) == (281455347137349 : BitVec 48)) && ((s &&& (1 : BitVec 12)) != 0 || (h &&& (19629343874 : BitVec 48)) == (19629343874 : BitVec 48)) && ((s &&& (16 : BitVec 12)) != 0 || (h &&& (229416 : BitVec 48)) == (229416 : BitVec 48)))) &&
  (!h.getLsbD 5 || (((s &&& (33 : BitVec 12)) != 0 || (h &&& (281435717793475 : BitVec 48)) == (281435717793475 : BitVec 48)) && ((s &&& (1 : BitVec 12)) != 0 || (h &&& (39258687748 : BitVec 48)) == (39258687748 : BitVec 48)) && ((s &&& (32 : BitVec 12)) != 0 || (h &&& (229400 : BitVec 48)) == (229400 : BitVec 48)))) &&
  (!h.getLsbD 6 || (((s &&& (2 : BitVec 12)) != 0 || (h &&& (9814671881 : BitVec 48)) == (9814671881 : BitVec 48)) && ((s &&& (10 : BitVec 12)) != 0 || (h &&& (281465160203318 : BitVec 48)) == (281465160203318 : BitVec 48)) && ((s &&& (8 : BitVec 12)) != 0 || (h &&& (1835392 : BitVec 48)) == (1835392 : BitVec 48)))) &&
  (!h.getLsbD 7 || (((s &&& (18 : BitVec 12)) != 0 || (h &&& (281455345531437 : BitVec 48)) == (281455345531437 : BitVec 48)) && ((s &&& (2 : BitVec 12)) != 0 || (h &&& (19629343762 : BitVec 48)) == (19629343762 : BitVec 48)) && ((s &&& (16 : BitVec 12)) != 0 || (h &&& (1835328 : BitVec 48)) == (1835328 : BitVec 48)))) &&
  (!h.getLsbD 8 || (((s &&& (34 : BitVec 12)) != 0 || (h &&& (281435716187675 : BitVec 48)) == (281435716187675 : BitVec 48)) && ((s &&& (2 : BitVec 12)) != 0 || (h &&& (39258687524 : BitVec 48)) == (39258687524 : BitVec 48)) && ((s &&& (32 : BitVec 12)) != 0 || (h &&& (1835200 : BitVec 48)) == (1835200 : BitVec 48)))) &&
  (!h.getLsbD 9 || (((s &&& (4 : BitVec 12)) != 0 || (h &&& (9814671433 : BitVec 48)) == (9814671433 : BitVec 48)) && ((s &&& (12 : BitVec 12)) != 0 || (h &&& (281465147355574 : BitVec 48)) == (281465147355574 : BitVec 48)) && ((s &&& (8 : BitVec 12)) != 0 || (h &&& (14683136 : BitVec 48)) == (14683136 : BitVec 48)))) &&
  (!h.getLsbD 10 || (((s &&& (20 : BitVec 12)) != 0 || (h &&& (281455332684141 : BitVec 48)) == (281455332684141 : BitVec 48)) && ((s &&& (4 : BitVec 12)) != 0 || (h &&& (19629342866 : BitVec 48)) == (19629342866 : BitVec 48)) && ((s &&& (16 : BitVec 12)) != 0 || (h &&& (14682624 : BitVec 48)) == (14682624 : BitVec 48)))) &&
  (!h.getLsbD 11 || (((s &&& (36 : BitVec 12)) != 0 || (h &&& (281435703341275 : BitVec 48)) == (281435703341275 : BitVec 48)) && ((s &&& (4 : BitVec 12)) != 0 || (h &&& (39258685732 : BitVec 48)) == (39258685732 : BitVec 48)) && ((s &&& (32 : BitVec 12)) != 0 || (h &&& (14681600 : BitVec 48)) == (14681600 : BitVec 48))))

def insideOK1 (s : BitVec 12) (h : BitVec 48) : Bool :=
  (!h.getLsbD 12 || (((s &&& (512 : BitVec 12)) != 0 || (h &&& (241274080423935 : BitVec 48)) == (241274080423935 : BitVec 48)) && ((s &&& (0 : BitVec 12)) != 0 || (h &&& (40200896282624 : BitVec 48)) == (40200896282624 : BitVec 48)))) &&
  (!h.getLsbD 13 || (((s &&& (1024 : BitVec 12)) != 0 || (h &&& (201073184137215 : BitVec 48)) == (201073184137215 : BitVec 48)) && ((s &&& (0 : BitVec 12)) != 0 || (h &&& (80401792565248 : BitVec 48)) == (80401792565248 : BitVec 48)))) &&
  (!h.getLsbD 14 || (((s &&& (2048 : BitVec 12)) != 0 || (h &&& (120671391563775 : BitVec 48)) == (120671391563775 : BitVec 48)) && ((s &&& (0 : BitVec 12)) != 0 || (h &&& (160803585130496 : BitVec 48)) == (160803585130496 : BitVec 48)))) &&
  (!h.getLsbD 15 || (((s &&& (513 : BitVec 12)) != 0 || (h &&& (241274080227271 : BitVec 48)) == (241274080227271 : BitVec 48)) && ((s &&& (512 : BitVec 12)) != 0 || (h &&& (196664 : BitVec 48)) == (196664 : BitVec 48)) && ((s &&& (1 : BitVec 12)) != 0 || (h &&& (40200896253952 : BitVec 48)) == (40200896253952 : BitVec 48)))) &&
  (!h.getLsbD 16 || (((s &&& (1025 : BitVec 12)) != 0 || (h &&& (201073183973319 : BitVec 48)) == (201073183973319 : BitVec 48)) && ((s &&& (1024 : BitVec 12)) != 0 || (h &&& (163896 : BitVec 48)) == (163896 : BitVec 48)) && ((s &&& (1 : BitVec 12)) != 0 || (h &&& (80401792507904 : BitVec 48)) == (80401792507904 : BitVec 48)))) &&
  (!h.getLsbD 17 || (((s &&& (2049 : BitVec 12)) != 0 || (h &&& (120671391465415 : BitVec 48)) == (120671391465415 : BitVec 48)) && ((s &&& (2048 : BitVec 12)) != 0 || (h &&& (98360 : BitVec 48)) == (98360 : BitVec 48)) && ((s &&& (1 : BitVec 12)) != 0 || (h &&& (160803585015808 : BitVec 48)) == (160803585015808 : BitVec 48)))) &&
  (!h.getLsbD 18 || (((s &&& (514 : BitVec 12)) != 0 || (h &&& (241274078850623 : BitVec 48)) == (241274078850623 : BitVec 48)) && ((s &&& (512 : BitVec 12)) != 0 || (h &&& (1573312 : BitVec 48)) == (1573312 : BitVec 48)) && ((s &&& (2 : BitVec 12)) != 0 || (h &&& (40200896024576 : BitVec 48)) == (40200896024576 : BitVec 48)))) &&
  (!h.getLsbD 19 || (((s &&& (1026 : BitVec 12)) != 0 || (h &&& (201073182826047 : BitVec 48)) == (201073182826047 : BitVec 48)) && ((s &&& (1024 : BitVec 12)) != 0 || (h &&& (1311168 : BitVec 48)) == (1311168 : BitVec 48)) && ((s &&& (2 : BitVec 12)) != 0 || (h &&& (80401792049152 : BitVec 48)) == (80401792049152 : BitVec 48)))) &&
  (!h.getLsbD 20 || (((s &&& (2050 : BitVec 12)) != 0 || (h &&& (120671390776895 : BitVec 48)) == (120671390776895 : BitVec 48)) && ((s &&& (2048 : BitVec 12)) != 0 || (h &&& (786880 : BitVec 48)) == (786880 : BitVec 48)) && ((s &&& (2 : BitVec 12)) != 0 || (h &&& (160803584098304 : BitVec 48)) == (160803584098304 : BitVec 48)))) &&
  (!h.getLsbD 21 || (((s &&& (516 : BitVec 12)) != 0 || (h &&& (241274067837439 : BitVec 48)) == (241274067837439 : BitVec 48)) && ((s &&& (512 : BitVec 12)) != 0 || (h &&& (12586496 : BitVec 48)) == (12586496 : BitVec 48)) && ((s &&& (4 : BitVec 12)) != 0 || (h &&& (40200894189568 : BitVec 48)) == (40200894189568 : BitVec 48)))) &&
  (!h.getLsbD 22 || (((s &&& (1028 : BitVec 12)) != 0 || (h &&& (201073173647871 : BitVec 48)) == (201073173647871 : BitVec 48)) && ((s &&& (1024 : BitVec 12)) != 0 || (h &&& (10489344 : BitVec 48)) == (10489344 : BitVec 48)) && ((s &&& (4 : BitVec 12)) != 0 || (h &&& (80401788379136 : BitVec 48)) == (80401788379136 : BitVec 48)))) &&
  (!h.getLsbD 23 || (((s &&& (2052 : BitVec 12)) != 0 || (h &&& (120671385268735 : BitVec 48)) == (120671385268735 : BitVec 48)) && ((s &&& (2048 : BitVec 12)) != 0 || (h &&& (6295040 : BitVec 48)) == (6295040 : BitVec 48)) && ((s &&& (4 : BitVec 12)) != 0 || (h &&& (160803576758272 : BitVec 48)) == (160803576758272 : BitVec 48))))

def insideOK2 (s : BitVec 12) (h : BitVec 48) : Bool :=
  (!h.getLsbD 24 || (((s &&& (0 : BitVec 12)) != 0 || (h &&& (9797894729 : BitVec 48)) == (9797894729 : BitVec 48)) && ((s &&& (8 : BitVec 12)) != 0 || (h &&& (281465162038710 : BitVec 48)) == (281465162038710 : BitVec 48)))) &&
  (!h.getLsbD 25 || (((s &&& (16 : BitVec 12)) != 0 || (h &&& (281455347366765 : BitVec 48)) == (281455347366765 : BitVec 48)) && ((s &&& (0 : BitVec 12)) != 0 || (h &&& (19595789458 : BitVec 48)) == (19595789458 : BitVec 48)))) &&
  (!h.getLsbD 26 || (((s &&& (32 : BitVec 12)) != 0 || (h &&& (281435718022875 : BitVec 48)) == (281435718022875 : BitVec 48)) && ((s &&& (0 : BitVec 12)) != 0 || (h &&& (39191578916 : BitVec 48)) == (39191578916 : BitVec 48)))) &&
  (!h.getLsbD 27 || (((s &&& (64 : BitVec 12)) != 0 || (h &&& (9680454217 : BitVec 48)) == (9680454217 : BitVec 48)) && ((s &&& (72 : BitVec 12)) != 0 || (h &&& (277616066035126 : BitVec 48)) == (277616066035126 : BitVec 48)) && ((s &&& (8 : BitVec 12)) != 0 || (h &&& (3849096003584 : BitVec 48)) == (3849096003584 : BitVec 48)))) &&
  (!h.getLsbD 28 || (((s &&& (80 : BitVec 12)) != 0 || (h &&& (277606385580909 : BitVec 48)) == (277606385580909 : BitVec 48)) && ((s &&& (64 : BitVec 12)) != 0 || (h &&& (19360908434 : BitVec 48)) == (19360908434 : BitVec 48)) && ((s &&& (16 : BitVec 12)) != 0 || (h &&& (3848961785856 : BitVec 48)) == (3848961785856 : BitVec 48)))) &&
  (!h.getLsbD 29 || (((s &&& (96 : BitVec 12)) != 0 || (h &&& (277587024672475 : BitVec 48)) == (277587024672475 : BitVec 48)) && ((s &&& (64 : BitVec 12)) != 0 || (h &&& (38721816868 : BitVec 48)) == (38721816868 : BitVec 48)) && ((s &&& (32 : BitVec 12)) != 0 || (h &&& (3848693350400 : BitVec 48)) == (3848693350400 : BitVec 48)))) &&
  (!h.getLsbD 30 || (((s &&& (128 : BitVec 12)) != 0 || (h &&& (8740930121 : BitVec 48)) == (8740930121 : BitVec 48)) && ((s &&& (136 : BitVec 12)) != 0 || (h &&& (250672394010038 : BitVec 48)) == (250672394010038 : BitVec 48)) && ((s &&& (8 : BitVec 12)) != 0 || (h &&& (30792768028672 : BitVec 48)) == (30792768028672 : BitVec 48)))) &&
  (!h.getLsbD 31 || (((s &&& (144 : BitVec 12)) != 0 || (h &&& (250663653079917 : BitVec 48)) == (250663653079917 : BitVec 48)) && ((s &&& (128 : BitVec 12)) != 0 || (h &&& (17481860242 : BitVec 48)) == (17481860242 : BitVec 48)) && ((s &&& (16 : BitVec 12)) != 0 || (h &&& (30791694286848 : BitVec 48)) == (30791694286848 : BitVec 48)))) &&
  (!h.getLsbD 32 || (((s &&& (160 : BitVec 12)) != 0 || (h &&& (250646171219675 : BitVec 48)) == (250646171219675 : BitVec 48)) && ((s &&& (128 : BitVec 12)) != 0 || (h &&& (34963720484 : BitVec 48)) == (34963720484 : BitVec 48)) && ((s &&& (32 : BitVec 12)) != 0 || (h &&& (30789546803200 : BitVec 48)) == (30789546803200 : BitVec 48)))) &&
  (!h.getLsbD 33 || (((s &&& (256 : BitVec 12)) != 0 || (h &&& (1224737353 : BitVec 48)) == (1224737353 : BitVec 48)) && ((s &&& (264 : BitVec 12)) != 0 || (h &&& (35123017809334 : BitVec 48)) == (35123017809334 : BitVec 48)) && ((s &&& (8 : BitVec 12)) != 0 || (h &&& (246342144229376 : BitVec 48)) == (246342144229376 : BitVec 48)))) &&
  (!h.getLsbD 34 || (((s &&& (272 : BitVec 12)) != 0 || (h &&& (35121793071981 : BitVec 48)) == (35121793071981 : BitVec 48)) && ((s &&& (256 : BitVec 12)) != 0 || (h &&& (2449474706 : BitVec 48)) == (2449474706 : BitVec 48)) && ((s &&& (16 : BitVec 12)) != 0 || (h &&& (246333554294784 : BitVec 48)) == (246333554294784 : BitVec 48)))) &&
  (!h.getLsbD 35 || (((s &&& (288 : BitVec 12)) != 0 || (h &&& (35119343597275 : BitVec 48)) == (35119343597275 : BitVec 48)) && ((s &&& (256 : BitVec 12)) != 0 || (h &&& (4898949412 : BitVec 48)) == (4898949412 : BitVec 48)) && ((s &&& (32 : BitVec 12)) != 0 || (h &&& (246316374425600 : BitVec 48)) == (246316374425600 : BitVec 48))))

def insideOK3 (s : BitVec 12) (h : BitVec 48) : Bool :=
  (!h.getLsbD 36 || (((s &&& (512 : BitVec 12)) != 0 || (h &&& (241274080423935 : BitVec 48)) == (241274080423935 : BitVec 48)) && ((s &&& (0 : BitVec 12)) != 0 || (h &&& (40132176809984 : BitVec 48)) == (40132176809984 : BitVec 48)))) &&
  (!h.getLsbD 37 || (((s &&& (1024 : BitVec 12)) != 0 || (h &&& (201073184137215 : BitVec 48)) == (201073184137215 : BitVec 48)) && ((s &&& (0 : BitVec 12)) != 0 || (h &&& (80264353619968 : BitVec 48)) == (80264353619968 : BitVec 48)))) &&
  (!h.getLsbD 38 || (((s &&& (2048 : BitVec 12)) != 0 || (h &&& (120671391563775 : BitVec 48)) == (120671391563775 : BitVec 48)) && ((s &&& (0 : BitVec 12)) != 0 || (h &&& (160528707239936 : BitVec 48)) == (160528707239936 : BitVec 48)))) &&
  (!h.getLsbD 39 || (((s &&& (576 : BitVec 12)) != 0 || (h &&& (237974606016511 : BitVec 48)) == (237974606016511 : BitVec 48)) && ((s &&& (64 : BitVec 12)) != 0 || (h &&& (39651140472832 : BitVec 48)) == (39651140472832 : BitVec 48)) && ((s &&& (512 : BitVec 12)) != 0 || (h &&& (3299474407424 : BitVec 48)) == (3299474407424 : BitVec 48)))) &&
  (!h.getLsbD 40 || (((s &&& (1088 : BitVec 12)) != 0 || (h &&& (198323465543679 : BitVec 48)) == (198323465543679 : BitVec 48)) && ((s &&& (64 : BitVec 12)) != 0 || (h &&& (79302280945664 : BitVec 48)) == (79302280945664 : BitVec 48)) && ((s &&& (1024 : BitVec 12)) != 0 || (h &&& (2749718593536 : BitVec 48)) == (2749718593536 : BitVec 48)))) &&
  (!h.getLsbD 41 || (((s &&& (2112 : BitVec 12)) != 0 || (h &&& (119021184598015 : BitVec 48)) == (119021184598015 : BitVec 48)) && ((s &&& (64 : BitVec 12)) != 0 || (h &&& (158604561891328 : BitVec 48)) == (158604561891328 : BitVec 48)) && ((s &&& (2048 : BitVec 12)) != 0 || (h &&& (1650206965760 : BitVec 48)) == (1650206965760 : BitVec 48)))) &&
  (!h.getLsbD 42 || (((s &&& (640 : BitVec 12)) != 0 || (h &&& (214878285164543 : BitVec 48)) == (214878285164543 : BitVec 48)) && ((s &&& (128 : BitVec 12)) != 0 || (h &&& (35802849775616 : BitVec 48)) == (35802849775616 : BitVec 48)) && ((s &&& (512 : BitVec 12)) != 0 || (h &&& (26395795259392 : BitVec 48)) == (26395795259392 : BitVec 48)))) &&
  (!h.getLsbD 43 || (((s &&& (1152 : BitVec 12)) != 0 || (h &&& (179075435388927 : BitVec 48)) == (179075435388927 : BitVec 48)) && ((s &&& (128 : BitVec 12)) != 0 || (h &&& (71605699551232 : BitVec 48)) == (71605699551232 : BitVec 48)) && ((s &&& (1024 : BitVec 12)) != 0 || (h &&& (21997748748288 : BitVec 48)) == (21997748748288 : BitVec 48)))) &&
  (!h.getLsbD 44 || (((s &&& (2176 : BitVec 12)) != 0 || (h &&& (107469735837695 : BitVec 48)) == (107469735837695 : BitVec 48)) && ((s &&& (128 : BitVec 12)) != 0 || (h &&& (143211399102464 : BitVec 48)) == (143211399102464 : BitVec 48)) && ((s &&& (2048 : BitVec 12)) != 0 || (h &&& (13201655726080 : BitVec 48)) == (13201655726080 : BitVec 48)))) &&
  (!h.getLsbD 45 || (((s &&& (768 : BitVec 12)) != 0 || (h &&& (30107718348799 : BitVec 48)) == (30107718348799 : BitVec 48)) && ((s &&& (256 : BitVec 12)) != 0 || (h &&& (5016524197888 : BitVec 48)) == (5016524197888 : BitVec 48)) && ((s &&& (512 : BitVec 12)) != 0 || (h &&& (211166362075136 : BitVec 48)) == (211166362075136 : BitVec 48)))) &&
  (!h.getLsbD 46 || (((s &&& (1280 : BitVec 12)) != 0 || (h &&& (25091194150911 : BitVec 48)) == (25091194150911 : BitVec 48)) && ((s &&& (256 : BitVec 12)) != 0 || (h &&& (10033048395776 : BitVec 48)) == (10033048395776 : BitVec 48)) && ((s &&& (1024 : BitVec 12)) != 0 || (h &&& (175981989986304 : BitVec 48)) == (175981989986304 : BitVec 48)))) &&
  (!h.getLsbD 47 || (((s &&& (2304 : BitVec 12)) != 0 || (h &&& (15058145755135 : BitVec 48)) == (15058145755135 : BitVec 48)) && ((s &&& (256 : BitVec 12)) != 0 || (h &&& (20066096791552 : BitVec 48)) == (20066096791552 : BitVec 48)) && ((s &&& (2048 : BitVec 12)) != 0 || (h &&& (105613245808640 : BitVec 48)) == (105613245808640 : BitVec 48))))

def insideOK (s : BitVec 12) (h : BitVec 48) : Bool :=
  insideOK0 s h &&
  insideOK1 s h &&
  insideOK2 s h &&
  insideOK3 s h

def outsideOK0 (s : BitVec 12) (h : BitVec 48) : Bool :=
  ((s &&& (1 : BitVec 12)) != (1 : BitVec 12) || ((h &&& (9814671945 : BitVec 48)) == (8 : BitVec 48))) &&
  ((s &&& (9 : BitVec 12)) != (9 : BitVec 12) || ((h &&& (61013080437006 : BitVec 48)) == (8 : BitVec 48))) &&
  ((s &&& (8 : BitVec 12)) != (8 : BitVec 12) || ((h &&& (229432 : BitVec 48)) == (8 : BitVec 48))) &&
  ((s &&& (18 : BitVec 12)) != (18 : BitVec 12) || ((h &&& (61003264160421 : BitVec 48)) == (128 : BitVec 48))) &&
  ((s &&& (2 : BitVec 12)) != (2 : BitVec 12) || ((h &&& (19629342866 : BitVec 48)) == (128 : BitVec 48))) &&
  ((s &&& (16 : BitVec 12)) != (16 : BitVec 12) || ((h &&& (16517056 : BitVec 48)) == (1152 : BitVec 48))) &&
  ((s &&& (20 : BitVec 12)) != (20 : BitVec 12) || ((h &&& (61003251316069 : BitVec 48)) == (1024 : BitVec 48))) &&
  ((s &&& (4 : BitVec 12)) != (4 : BitVec 12) || ((h &&& (58888031542 : BitVec 48)) == (3072 : BitVec 48))) &&
  ((s &&& (36 : BitVec 12)) != (36 : BitVec 12) || ((h &&& (60983621974099 : BitVec 48)) == (2048 : BitVec 48))) &&
  ((s &&& (32 : BitVec 12)) != (32 : BitVec 12) || ((h &&& (14682624 : BitVec 48)) == (2048 : BitVec 48))) &&
  ((s &&& (576 : BitVec 12)) != (576 : BitVec 12) || ((h &&& (18622036271991 : BitVec 48)) == (549755813888 : BitVec 48))) &&
  ((s &&& (64 : BitVec 12)) != (64 : BitVec 12) || ((h &&& (40200896286720 : BitVec 48)) == (549755813888 : BitVec 48)))

def outsideOK1 (s : BitVec 12) (h : BitVec 48) : Bool :=
  ((s &&& (512 : BitVec 12)) != (512 : BitVec 12) || ((h &&& (3849230221312 : BitVec 48)) == (549755813888 : BitVec 48))) &&
  ((s &&& (1152 : BitVec 12)) != (1152 : BitVec 12) || ((h &&& (46584284238711 : BitVec 48)) == (8796093022208 : BitVec 48))) &&
  ((s &&& (128 : BitVec 12)) != (128 : BitVec 12) || ((h &&& (10033048395776 : BitVec 48)) == (8796093022208 : BitVec 48))) &&
  ((s &&& (1024 : BitVec 12)) != (1024 : BitVec 12) || ((h &&& (136407087579136 : BitVec 48)) == (79164837199872 : BitVec 48))) &&
  ((s &&& (1280 : BitVec 12)) != (1280 : BitVec 12) || ((h &&& (94910182511479 : BitVec 48)) == (70368744177664 : BitVec 48))) &&
  ((s &&& (256 : BitVec 12)) != (256 : BitVec 12) || ((h &&& (232409284698112 : BitVec 48)) == (211106232532992 : BitVec 48))) &&
  ((s &&& (2304 : BitVec 12)) != (2304 : BitVec 12) || ((h &&& (146449785271159 : BitVec 48)) == (140737488355328 : BitVec 48))) &&
  ((s &&& (2048 : BitVec 12)) != (2048 : BitVec 12) || ((h &&& (175981989986304 : BitVec 48)) == (140737488355328 : BitVec 48)))

def outsideOK (s : BitVec 12) (h : BitVec 48) : Bool :=
  outsideOK0 s h &&
  outsideOK1 s h

def sig0 (h : BitVec 48) : BitVec 7 := h.extractLsb' 11 1 ++ h.extractLsb' 10 1 ++ h.extractLsb' 9 1 ++ h.extractLsb' 8 1 ++ h.extractLsb' 7 1 ++ h.extractLsb' 4 1 ++ h.extractLsb' 3 1

def sig1 (h : BitVec 48) : BitVec 7 := h.extractLsb' 47 1 ++ h.extractLsb' 46 1 ++ h.extractLsb' 45 1 ++ h.extractLsb' 44 1 ++ h.extractLsb' 43 1 ++ h.extractLsb' 40 1 ++ h.extractLsb' 39 1

def rowMask (s : BitVec 6) : Bool :=
  (s == 1 || s == 2 || s == 4)

def columnMask (s : BitVec 6) : Bool :=
  (s == 8 || s == 16 || s == 32)

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000
theorem compatibility (a b : BitVec 6) (h : BitVec 48)
    (hi : insideOK (b ++ a) h = true) (ho : outsideOK (b ++ a) h = true)
    (ca : costOK a (sig0 h) = true) (cb : costOK b (sig1 h) = true) :
    (rowMask a && columnMask b || columnMask a && rowMask b || (a == 9 && b == 9)) = true := by
  unfold columnMask rowMask outsideOK outsideOK1 outsideOK0 insideOK insideOK3 insideOK2 insideOK1 insideOK0 at *
  unfold costOK sig0 sig1 at *
  bv_decide

def allowed (a b : BitVec 6) : Prop :=
  (rowMask a && columnMask b || columnMask a && rowMask b || (a == 9 && b == 9)) = true

theorem triangle (a b c : BitVec 6) (ab : allowed a b) (bc : allowed b c)
    (ac : allowed a c) : a = 9 ∧ b = 9 ∧ c = 9 := by
  have disjoint : ∀ x : BitVec 6, rowMask x = true → columnMask x = true → False := by decide +kernel
  have nine : rowMask 9 = false ∧ columnMask 9 = false := by decide +kernel
  simp only [allowed, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at ab bc ac
  grind

#print axioms triangle
#print axioms compatibility
end Alexrollo64.PairFilter
