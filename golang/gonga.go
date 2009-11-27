// Original Ngaro, RetroForth, Uki, ...
//	Copyright (C) 2008, 2009, Charles Childers
// Go port
//	Copyright 2009 JGL
// Public Domain or LICENSE file

// TODO:
//	- cat multiple image files
//	- builtin image optional
//	- ...
//	- multi-core

package main

import (
	"./_obj/ngaro";
	"bufio";
	"flag";
	"fmt";
	"io";
	"os";
)

var size = flag.Int("s", 50000, "image size")

func readIn(vm *ngaro.NgaroVM) {
	r := bufio.NewReader(os.Stdin);
	b := make([]byte, 1);
	for {
		_, err := io.ReadAtLeast(r, b, 1);
		if err != nil {
			vm.Off <- true;
		}
		vm.In <- int(b[0]);
	}
}

func printOut(vm *ngaro.NgaroVM) {
	for {
		fmt.Print(string(<-vm.Out))
	}
}

func main() {
	// cat retro-10.2.1/vm/javascript/retroImage.js | awk -F'(\\]=)|;|\\[' '/^image/ { if(p) {p = p ","}; for(i=0;i<$2-n;i++) {p = p "0,"}; p = p $3; n=$2+1 }; END { print "retroImage := []int{" p "};" }'
	retroImage := []int{8, 1774, 2692, 5120, 0, 0, 0, 82, 69, 84, 82, 79, 32, 49, 48, 0, 87, 111, 114, 100, 32, 78, 111, 116, 32, 70, 111, 117, 110, 100, 0, 111, 107, 32, 0, 0, 0, 2, 9, 0, 0, 26, 9, 0, 0, 27, 9, 0, 0, 4, 9, 0, 0, 3, 9, 0, 0, 20, 9, 0, 0, 21, 9, 0, 0, 22, 9, 0, 0, 14, 9, 0, 0, 15, 9, 0, 0, 16, 9, 0, 0, 17, 9, 0, 0, 18, 9, 0, 0, 19, 9, 0, 0, 23, 9, 0, 0, 24, 9, 0, 0, 29, 9, 0, 0, 28, 9, 0, 0, 1, 0, 1, 0, 29, 30, 9, 0, 0, 4, 3, 9, 0, 0, 5, 2, 6, 4, 9, 0, 0, 3, 3, 9, 0, 0, 1, -1, 22, 9, 0, 0, 5, 4, 6, 4, 9, 0, 0, 4, 5, 4, 6, 9, 0, 0, 2, 7, 146, 9, 0, 0, 7, 121, 7, 121, 9, 0, 0, 1, -1, 4, 15, 9, 0, 0, 1, 0, 4, 15, 9, 0, 0, 19, 7, 116, 9, 0, 0, 19, 3, 9, 0, 0, 1, -1, 18, 9, 0, 0, 27, 5, 9, 0, 0, 2, 26, 4, 14, 9, 0, 0, 2, 26, 5, 15, 6, 9, 0, 0, 2, 5, 14, 16, 6, 15, 9, 0, 0, 2, 5, 14, 4, 17, 6, 15, 9, 0, 0, 1, 3, 14, 9, 0, 0, 7, 236, 15, 7, 236, 26, 1, 3, 15, 9, 0, 0, 1, -1, 1, 5, 15, 9, 0, 0, 1, 0, 1, 5, 15, 9, 0, 0, 1, 9, 7, 242, 9, 0, 0, 7, 270, 7, 262, 9, 0, 0, 2, 14, 25, 7, 242, 26, 8, 286, 9, 0, 0, 7, 284, 3, 1, 0, 7, 242, 9, 0, 0, 1, 5, 7, 242, 9, 0, 0, 1, 6, 7, 242, 9, 0, 0, 1, 7, 7, 242, 7, 242, 9, 0, 0, 1, 1, 7, 242, 7, 242, 9, 0, 0, 7, 236, 1, 5, 7, 242, 9, 0, 0, 1, 6, 7, 242, 1, 27, 7, 242, 1, 2, 7, 242, 1, 1, 7, 242, 1, 0, 7, 242, 1, 12, 7, 242, 7, 242, 1, 3, 7, 242, 9, 0, 0, 7, 236, 1, 0, 7, 242, 9, 0, 0, 1, 12, 7, 242, 7, 379, 9, 0, 0, 1, 11, 7, 242, 7, 379, 9, 0, 0, 1, 10, 7, 242, 7, 379, 9, 0, 0, 1, 13, 7, 242, 7, 379, 9, 0, 0, 7, 236, 4, 15, 1, 0, 7, 242, 9, 0, 0, 7, 236, 9, 0, 0, 1, 8, 7, 242, 7, 242, 9, 0, 0, 1, 25, 7, 242, 9, 0, 0, 1, 5, 14, 1, -1, 12, 472, 1, 7, 7, 242, 7, 242, 9, 0, 7, 197, 9, 0, 0, 2, 14, 1, 0, 13, 487, 7, 456, 9, 0, 1, 5, 14, 1, -1, 12, 501, 26, 26, 14, 7, 242, 9, 0, 7, 197, 9, 0, 0, 7, 197, 9, 0, 0, 1, 5, 14, 1, -1, 12, 525, 1, 1, 7, 242, 7, 242, 0, 9, 0, 0, 1, 5, 14, 1, 0, 12, 539, 7, 51, 9, 0, 7, 197, 9, 0, 0, 0, -1, 0, 0, 1, 546, 14, 25, 3, 1, 0, 1, 3, 29, 9, 0, 0, 1, 1, 1, 2, 29, 7, 107, 7, 547, 9, 0, 0, 1, 10, 7, 560, 9, 0, 0, 1, -1, 7, 560, 9, 0, 0, 7, 202, 25, 7, 560, 8, 588, 9, 0, 0, 1, 546, 7, 173, 7, 586, 3, 1, 546, 7, 166, 7, 547, 9, 0, 0, -1, 0, 0, 9, 0, 0, 2, 1, 13, 12, 628, 3, 1, 10, 0, 9, 0, 0, 1, 614, 14, 25, 3, 2, 1, 9, 12, 646, 3, 1, 32, 9, 0, 2, 1, 10, 12, 656, 3, 1, 32, 9, 0, 9, 0, 0, 1, 1, 1, 1, 29, 7, 107, 1, 1, 28, 2, 1, 0, 13, 682, 7, 615, 7, 618, 7, 630, 9, 0, 3, 8, 660, 9, 0, 0, 1, 4096, 1, 612, 14, 16, 15, 9, 0, 0, 1, 1, 1, 612, 7, 217, 9, 0, 0, 7, 658, 2, 7, 560, 2, 1, 613, 14, 13, 724, 7, 687, 7, 697, 9, 0, 3, 8, 708, 9, 0, 0, 7, 658, 2, 7, 560, 2, 1, 613, 14, 12, 744, 3, 9, 0, 2, 1, 8, 12, 759, 1, 1, 1, 612, 7, 226, 3, 8, 729, 0, 7, 687, 7, 697, 8, 731, 9, 0, 0, 1, 613, 15, 1, 0, 1, 612, 15, 7, 706, 7, 729, 1, 0, 7, 687, 9, 0, 0, 26, 9, 0, 0, 26, 26, 9, 0, 0, 26, 26, 26, 9, 0, 0, 7, 236, 1, 2, 14, 7, 242, 1, 2, 15, 1, 510, 7, 242, 7, 236, 1, 0, 7, 242, 1, 32, 7, 767, 1, 4096, 7, 295, 7, 236, 4, 15, 9, 0, 0, 1, 2, 14, 7, 786, 15, 7, 254, 1, 0, 7, 242, 1, 0, 7, 242, 9, 0, 0, 7, 801, 1, 456, 7, 836, 9, 0, 0, 7, 801, 1, 505, 7, 836, 9, 0, 0, 7, 801, 1, 527, 7, 836, 9, 0, 0, 1, 41, 7, 767, 9, 0, 0, 13, 898, 1, 0, 1, 6, 15, 0, 9, 0, 0, 14, 4, 14, 9, 0, 0, 26, 4, 26, 4, 9, 0, 0, 7, 159, 14, 4, 14, 16, 25, 3, 7, 159, 7, 900, 7, 889, 7, 906, 1, 6, 14, 25, 3, 8, 915, 9, 0, 0, 1, -1, 1, 6, 15, 7, 913, 7, 128, 1, 6, 14, 9, 0, 0, 2, 14, 25, 3, 7, 906, 8, 956, 9, 0, 0, 1, 0, 4, 7, 954, 3, 9, 0, 0, 0, 1, 3072, 1, 974, 15, 9, 0, 0, 1, 1, 1, 974, 7, 217, 9, 0, 0, 7, 202, 25, 1, 974, 14, 15, 7, 983, 8, 994, 9, 0, 0, 7, 975, 7, 992, 3, 1, 0, 1, 974, 14, 15, 1, 3072, 9, 0, 0, 2, 7, 965, 25, 5, 7, 202, 7, 242, 6, 27, 8, 1027, 9, 0, 0, 2, 7, 965, 26, 26, 26, 7, 236, 16, 1, 8, 7, 242, 7, 242, 7, 236, 5, 7, 1022, 3, 1, 0, 7, 242, 6, 9, 0, 0, 1, 34, 7, 767, 1, 4096, 7, 1006, 9, 0, 0, 7, 1067, 7, 1038, 1, 1, 7, 242, 7, 242, 9, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 65, 66, 67, 68, 69, 70, 0, 10, 0, 0, 2, 5, 1, 1095, 16, 14, 7, 121, 12, 1130, 1, -1, 1, 1092, 15, 0, 6, 25, 27, 8, 1115, 9, 0, 0, 1, 16, 7, 1113, 9, 0, 0, 1, 10, 7, 1113, 9, 0, 0, 1, 8, 7, 1113, 9, 0, 0, 1, 2, 7, 1113, 9, 0, 0, 1, 1112, 14, 1, 10, 12, 1177, 7, 1144, 9, 0, 1, 1112, 14, 1, 16, 12, 1188, 7, 1137, 9, 0, 1, 1112, 14, 1, 8, 12, 1199, 7, 1151, 9, 0, 1, 1112, 14, 1, 2, 12, 1210, 7, 1158, 9, 0, 9, 0, 0, 1, 0, 1, 1092, 15, 7, 1165, 3, 1, 1092, 14, 9, 0, 0, 1, 48, 17, 1, 1112, 14, 1, 16, 12, 1247, 2, 1, 16, 11, 1246, 1, 7, 17, 0, 0, 9, 0, 0, 2, 14, 1, 45, 12, 1264, 1, -1, 1, 1094, 15, 26, 9, 0, 1, 1, 1, 1094, 15, 9, 0, 0, 2, 14, 25, 7, 1226, 1, 1091, 14, 1, 1112, 14, 18, 16, 1, 1091, 15, 26, 8, 1273, 9, 0, 0, 7, 1249, 1, 0, 1, 1091, 15, 7, 1271, 3, 1, 1091, 14, 1, 1094, 14, 18, 9, 0, 0, 2, 14, 25, 7, 1212, 1, 6, 14, 20, 1, 6, 15, 26, 8, 1315, 9, 0, 0, 7, 1249, 1, -1, 1, 6, 15, 7, 1313, 3, 1, 6, 14, 9, 0, 0, 1, 1112, 14, 19, 4, 1, 1095, 16, 14, 4, 25, 8, 1349, 9, 0, 0, 2, 1, 0, 11, 1371, 9, 0, 1, 45, 7, 560, 1, -1, 18, 9, 0, 0, 25, 7, 560, 8, 1382, 9, 0, 0, 7, 1363, 1, 0, 7, 47, 7, 1347, 7, 1380, 1, 32, 7, 560, 9, 0, 0, 0, 2, 7, 795, 1, 4096, 7, 939, 1, -1, 12, 1427, 1, 4, 15, 1, 1405, 7, 166, 9, 0, 14, 25, 8, 1408, 9, 0, 0, 1, 1405, 7, 173, 1, 2, 14, 7, 1406, 9, 0, 0, 1, 32, 7, 767, 7, 1433, 1, 1405, 14, 1, -1, 12, 1467, 1, 4, 14, 7, 790, 14, 9, 0, 1, 0, 1, 1405, 7, 166, 9, 0, 0, 1, 1, 7, 242, 7, 1445, 7, 242, 9, 0, 0, 2, 1, 0, 4, 15, 26, 1, 0, 4, 15, 9, 0, 0, 2, 1, 8, 4, 15, 26, 15, 9, 0, 0, 7, 1445, 7, 1486, 9, 0, 0, 7, 1445, 7, 1499, 9, 0, 0, 1, 1, 1, 4, 29, 7, 107, 9, 0, 0, 8, 5000000, 9, 0, 0, 1, 2, 14, 2, 7, 795, 7, 596, 1, 32, 7, 560, 14, 25, 8, 1543, 9, 0, 0, 1, -5, 1, 5, 29, 30, 1, 5, 28, 9, 0, 0, 7, 1557, 0, 0, 25, 5, 3, 6, 27, 7, 1573, 9, 0, 0, 0, 1, 7, 7, 596, 7, 572, 9, 0, 0, 1, -1, 1, 5, 29, 7, 107, 1, 5, 28, 1, 1583, 15, 1, -2, 1, 5, 29, 7, 107, 1, 5, 28, 1, 543, 15, 1, -3, 1, 5, 29, 7, 107, 1, 5, 28, 1, 544, 15, 1, -4, 1, 5, 29, 7, 107, 1, 5, 28, 1, 545, 15, 7, 1584, 9, 0, 0, 7, 197, 9, 0, 0, 7, 572, 1, 16, 7, 596, 7, 572, 9, 0, 0, 1, 4, 14, 7, 790, 14, 9, 0, 0, 1, 4, 14, 7, 786, 14, 9, 0, 0, 1, 4096, 7, 1331, 9, 0, 0, 1, 4096, 7, 1293, 7, 510, 9, 0, 0, 1, 1405, 14, 1, -1, 12, 1715, 7, 1666, 7, 1675, 7, 1650, 0, 9, 0, 0, 1, 1405, 14, 1, 0, 12, 1738, 7, 1684, 1, -1, 12, 1735, 7, 1691, 9, 0, 7, 1655, 0, 9, 0, 0, 1, 5, 14, 1, 0, 12, 1755, 7, 572, 1, 31, 7, 596, 0, 9, 0, 0, 7, 1740, 1, 32, 7, 767, 7, 1433, 7, 1700, 7, 1717, 8, 1759, 9, 7, 1593, 7, 1757, 0, 476, 39, 49, 43, 0, 1778, 476, 43, 49, 45, 0, 1784, 476, 47, 115, 119, 97, 112, 0, 1790, 476, 51, 100, 114, 111, 112, 0, 1798, 476, 55, 97, 110, 100, 0, 1806, 476, 59, 111, 114, 0, 1813, 476, 63, 120, 111, 114, 0, 1819, 476, 67, 64, 0, 1826, 476, 71, 33, 0, 1831, 476, 75, 43, 0, 1836, 476, 79, 45, 0, 1841, 476, 83, 42, 0, 1846, 476, 87, 47, 109, 111, 100, 0, 1851, 476, 91, 60, 60, 0, 1859, 476, 95, 62, 62, 0, 1865, 476, 35, 100, 117, 112, 0, 1871, 476, 103, 105, 110, 0, 1878, 476, 99, 111, 117, 116, 0, 1884, 456, 236, 104, 101, 114, 101, 0, 1891, 456, 242, 44, 0, 1899, 456, 254, 93, 0, 1904, 456, 801, 99, 114, 101, 97, 116, 101, 0, 1909, 456, 855, 58, 0, 1919, 456, 864, 109, 97, 99, 114, 111, 58, 0, 1924, 456, 873, 99, 111, 109, 112, 105, 108, 101, 114, 58, 0, 1934, 456, 767, 97, 99, 99, 101, 112, 116, 0, 1947, 456, 572, 99, 114, 0, 1957, 456, 560, 101, 109, 105, 116, 0, 1963, 456, 596, 116, 121, 112, 101, 0, 1971, 456, 579, 99, 108, 101, 97, 114, 0, 1979, 456, 1538, 119, 111, 114, 100, 115, 0, 1988, 456, 658, 107, 101, 121, 0, 1997, 456, 121, 111, 118, 101, 114, 0, 2004, 456, 128, 50, 100, 114, 111, 112, 0, 2012, 456, 133, 110, 111, 116, 0, 2021, 456, 139, 114, 111, 116, 0, 2028, 456, 146, 45, 114, 111, 116, 0, 2035, 456, 153, 116, 117, 99, 107, 0, 2043, 456, 159, 50, 100, 117, 112, 0, 2051, 456, 166, 111, 110, 0, 2059, 456, 173, 111, 102, 102, 0, 2065, 456, 180, 47, 0, 2072, 456, 186, 109, 111, 100, 0, 2077, 456, 191, 110, 101, 103, 0, 2084, 456, 197, 101, 120, 101, 99, 117, 116, 101, 0, 2091, 456, 1388, 46, 0, 2102, 456, 1067, 34, 0, 2107, 456, 939, 99, 111, 109, 112, 97, 114, 101, 0, 2112, 456, 107, 119, 97, 105, 116, 0, 2123, 456, 1445, 39, 0, 2131, 456, 202, 64, 43, 0, 2136, 456, 209, 33, 43, 0, 2142, 456, 217, 43, 33, 0, 2148, 456, 226, 45, 33, 0, 2154, 456, 1499, 58, 105, 115, 0, 2160, 456, 1486, 58, 100, 101, 118, 101, 99, 116, 111, 114, 0, 2167, 456, 1516, 105, 115, 0, 2180, 456, 1509, 100, 101, 118, 101, 99, 116, 111, 114, 0, 2186, 456, 319, 99, 111, 109, 112, 105, 108, 101, 0, 2198, 456, 328, 108, 105, 116, 101, 114, 97, 108, 44, 0, 2209, 456, 1006, 116, 101, 109, 112, 83, 116, 114, 105, 110, 103, 0, 2221, 456, 547, 114, 101, 100, 114, 97, 119, 0, 2235, 456, 1038, 107, 101, 101, 112, 83, 116, 114, 105, 110, 103, 0, 2245, 456, 965, 103, 101, 116, 76, 101, 110, 103, 116, 104, 0, 2259, 456, 1533, 98, 121, 101, 0, 2272, 456, 615, 40, 114, 101, 109, 97, 112, 45, 107, 101, 121, 115, 41, 0, 2279, 456, 1650, 119, 105, 116, 104, 45, 99, 108, 97, 115, 115, 0, 2295, 456, 456, 46, 119, 111, 114, 100, 0, 2309, 456, 505, 46, 109, 97, 99, 114, 111, 0, 2318, 456, 510, 46, 100, 97, 116, 97, 0, 2328, 456, 476, 46, 105, 110, 108, 105, 110, 101, 0, 2337, 456, 527, 46, 99, 111, 109, 112, 105, 108, 101, 114, 0, 2348, 456, 786, 100, 45, 62, 99, 108, 97, 115, 115, 0, 2361, 456, 790, 100, 45, 62, 120, 116, 0, 2373, 456, 795, 100, 45, 62, 110, 97, 109, 101, 0, 2382, 456, 1584, 98, 111, 111, 116, 0, 2393, 456, 1557, 100, 101, 112, 116, 104, 0, 2401, 456, 1569, 114, 101, 115, 101, 116, 0, 2410, 456, 1655, 110, 111, 116, 102, 111, 117, 110, 100, 0, 2419, 456, 1523, 115, 97, 118, 101, 0, 2431, 456, 1293, 62, 110, 117, 109, 98, 101, 114, 0, 2439, 456, 1740, 111, 107, 0, 2450, 456, 1757, 108, 105, 115, 116, 101, 110, 0, 2456, 456, 116, 110, 105, 112, 0, 2466, 527, 1078, 115, 34, 0, 2473, 527, 262, 91, 0, 2479, 527, 277, 59, 0, 2484, 527, 270, 59, 59, 0, 2489, 527, 388, 61, 105, 102, 0, 2495, 527, 397, 62, 105, 102, 0, 2502, 527, 406, 60, 105, 102, 0, 2509, 527, 415, 33, 105, 102, 0, 2516, 527, 424, 116, 104, 101, 110, 0, 2523, 527, 435, 114, 101, 112, 101, 97, 116, 0, 2531, 527, 440, 97, 103, 97, 105, 110, 0, 2541, 527, 449, 48, 59, 0, 2550, 527, 305, 112, 117, 115, 104, 0, 2556, 527, 312, 112, 111, 112, 0, 2564, 527, 1475, 91, 39, 93, 0, 2571, 527, 337, 102, 111, 114, 0, 2578, 527, 346, 110, 101, 120, 116, 0, 2585, 505, 882, 40, 0, 2593, 510, 2, 108, 97, 115, 116, 0, 2598, 510, 5, 99, 111, 109, 112, 105, 108, 101, 114, 0, 2606, 510, 4096, 116, 105, 98, 0, 2618, 510, 546, 117, 112, 100, 97, 116, 101, 0, 2625, 510, 543, 102, 98, 0, 2635, 510, 544, 102, 119, 0, 2641, 510, 545, 102, 104, 0, 2647, 510, 1583, 35, 109, 101, 109, 0, 2653, 510, 3, 104, 101, 97, 112, 0, 2661, 510, 4, 119, 104, 105, 99, 104, 0, 2669, 510, 614, 119, 104, 105, 116, 101, 115, 112, 97, 99, 101, 0, 2678, 510, 1112, 98, 97, 115, 101};
	flag.Parse();
	// image, _ := io.ReadFile(flag.Arg(0));
	vm := ngaro.NewVM(retroImage, *size);
	go readIn(vm);
	go printOut(vm);
	<-vm.Off;
	//D:println("Gonga: Bye!");
}
