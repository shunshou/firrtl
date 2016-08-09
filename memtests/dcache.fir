circuit DCacheDataArray:
  module DCacheDataArray : 
    input clk : Clock
    input reset : UInt<1>
    output io : {flip req : {valid : UInt<1>, bits : {addr : UInt<12>, write : UInt<1>, wdata : UInt<64>, wmask : UInt<8>, way_en : UInt<4>}}, resp : UInt<64>[4]}
    
    io is invalid
    node addr = shr(io.req.bits.addr, 3) @[dcache.scala 29:31] 
    smem T_406 : UInt<8>[8][512] @[dcache.scala 31:23] 
    node T_408 = bits(io.req.bits.way_en, 0, 0) @[dcache.scala 32:72] 
    node T_409 = or(UInt<1>("h00"), T_408) @[dcache.scala 32:51] 
    node T_410 = and(io.req.valid, T_409) @[dcache.scala 32:30] 
    node T_411 = and(T_410, io.req.bits.write) @[dcache.scala 33:17] 
    when T_411 : @[dcache.scala 33:39] 
      node T_412 = bits(io.req.bits.wdata, 7, 0) @[dcache.scala 34:63] 
      node T_413 = bits(io.req.bits.wdata, 15, 8) @[dcache.scala 34:63] 
      node T_414 = bits(io.req.bits.wdata, 23, 16) @[dcache.scala 34:63] 
      node T_415 = bits(io.req.bits.wdata, 31, 24) @[dcache.scala 34:63] 
      node T_416 = bits(io.req.bits.wdata, 39, 32) @[dcache.scala 34:63] 
      node T_417 = bits(io.req.bits.wdata, 47, 40) @[dcache.scala 34:63] 
      node T_418 = bits(io.req.bits.wdata, 55, 48) @[dcache.scala 34:63] 
      node T_419 = bits(io.req.bits.wdata, 63, 56) @[dcache.scala 34:63] 
      wire T_425 : UInt<8>[8] @[dcache.scala 34:40] 
      T_425 is invalid @[dcache.scala 34:40] 
      T_425[0] <= T_412 @[dcache.scala 34:40] 
      T_425[1] <= T_413 @[dcache.scala 34:40] 
      T_425[2] <= T_414 @[dcache.scala 34:40] 
      T_425[3] <= T_415 @[dcache.scala 34:40] 
      T_425[4] <= T_416 @[dcache.scala 34:40] 
      T_425[5] <= T_417 @[dcache.scala 34:40] 
      T_425[6] <= T_418 @[dcache.scala 34:40] 
      T_425[7] <= T_419 @[dcache.scala 34:40] 
      node T_427 = bits(io.req.bits.wmask, 0, 0) @[dcache.scala 35:49] 
      node T_428 = bits(io.req.bits.wmask, 1, 1) @[dcache.scala 35:49] 
      node T_429 = bits(io.req.bits.wmask, 2, 2) @[dcache.scala 35:49] 
      node T_430 = bits(io.req.bits.wmask, 3, 3) @[dcache.scala 35:49] 
      node T_431 = bits(io.req.bits.wmask, 4, 4) @[dcache.scala 35:49] 
      node T_432 = bits(io.req.bits.wmask, 5, 5) @[dcache.scala 35:49] 
      node T_433 = bits(io.req.bits.wmask, 6, 6) @[dcache.scala 35:49] 
      node T_434 = bits(io.req.bits.wmask, 7, 7) @[dcache.scala 35:49] 
      write mport T_437 = T_406[addr], clk
      when T_427 :
        T_437[0] <= T_425[0]
        skip
      when T_428 :
        T_437[1] <= T_425[1]
        skip
      when T_429 :
        T_437[2] <= T_425[2]
        skip
      when T_430 :
        T_437[3] <= T_425[3]
        skip
      when T_431 :
        T_437[4] <= T_425[4]
        skip
      when T_432 :
        T_437[5] <= T_425[5]
        skip
      when T_433 :
        T_437[6] <= T_425[6]
        skip
      when T_434 :
        T_437[7] <= T_425[7]
        skip
      skip @[dcache.scala 33:39] 
    node T_440 = eq(io.req.bits.write, UInt<1>("h00")) @[dcache.scala 37:45] 
    node T_441 = and(T_410, T_440) @[dcache.scala 37:42] 
    wire T_443 : UInt
    T_443 is invalid
    when T_441 :
      T_443 <= addr
      skip
    read mport T_446 = T_406[T_443], clk
    node T_448 = cat(T_446[1], T_446[0]) @[dcache.scala 37:65] 
    node T_449 = cat(T_446[3], T_446[2]) @[dcache.scala 37:65] 
    node T_450 = cat(T_449, T_448) @[dcache.scala 37:65] 
    node T_451 = cat(T_446[5], T_446[4]) @[dcache.scala 37:65] 
    node T_452 = cat(T_446[7], T_446[6]) @[dcache.scala 37:65] 
    node T_453 = cat(T_452, T_451) @[dcache.scala 37:65] 
    node T_454 = cat(T_453, T_450) @[dcache.scala 37:65] 
    io.resp[0] <= T_454 @[dcache.scala 37:16] 
    smem T_463 : UInt<8>[8][512] @[dcache.scala 31:23] 
    node T_465 = bits(io.req.bits.way_en, 1, 1) @[dcache.scala 32:72] 
    node T_466 = or(UInt<1>("h00"), T_465) @[dcache.scala 32:51] 
    node T_467 = and(io.req.valid, T_466) @[dcache.scala 32:30] 
    node T_468 = and(T_467, io.req.bits.write) @[dcache.scala 33:17] 
    when T_468 : @[dcache.scala 33:39] 
      node T_469 = bits(io.req.bits.wdata, 7, 0) @[dcache.scala 34:63] 
      node T_470 = bits(io.req.bits.wdata, 15, 8) @[dcache.scala 34:63] 
      node T_471 = bits(io.req.bits.wdata, 23, 16) @[dcache.scala 34:63] 
      node T_472 = bits(io.req.bits.wdata, 31, 24) @[dcache.scala 34:63] 
      node T_473 = bits(io.req.bits.wdata, 39, 32) @[dcache.scala 34:63] 
      node T_474 = bits(io.req.bits.wdata, 47, 40) @[dcache.scala 34:63] 
      node T_475 = bits(io.req.bits.wdata, 55, 48) @[dcache.scala 34:63] 
      node T_476 = bits(io.req.bits.wdata, 63, 56) @[dcache.scala 34:63] 
      wire T_482 : UInt<8>[8] @[dcache.scala 34:40] 
      T_482 is invalid @[dcache.scala 34:40] 
      T_482[0] <= T_469 @[dcache.scala 34:40] 
      T_482[1] <= T_470 @[dcache.scala 34:40] 
      T_482[2] <= T_471 @[dcache.scala 34:40] 
      T_482[3] <= T_472 @[dcache.scala 34:40] 
      T_482[4] <= T_473 @[dcache.scala 34:40] 
      T_482[5] <= T_474 @[dcache.scala 34:40] 
      T_482[6] <= T_475 @[dcache.scala 34:40] 
      T_482[7] <= T_476 @[dcache.scala 34:40] 
      node T_484 = bits(io.req.bits.wmask, 0, 0) @[dcache.scala 35:49] 
      node T_485 = bits(io.req.bits.wmask, 1, 1) @[dcache.scala 35:49] 
      node T_486 = bits(io.req.bits.wmask, 2, 2) @[dcache.scala 35:49] 
      node T_487 = bits(io.req.bits.wmask, 3, 3) @[dcache.scala 35:49] 
      node T_488 = bits(io.req.bits.wmask, 4, 4) @[dcache.scala 35:49] 
      node T_489 = bits(io.req.bits.wmask, 5, 5) @[dcache.scala 35:49] 
      node T_490 = bits(io.req.bits.wmask, 6, 6) @[dcache.scala 35:49] 
      node T_491 = bits(io.req.bits.wmask, 7, 7) @[dcache.scala 35:49] 
      write mport T_494 = T_463[addr], clk
      when T_484 :
        T_494[0] <= T_482[0]
        skip
      when T_485 :
        T_494[1] <= T_482[1]
        skip
      when T_486 :
        T_494[2] <= T_482[2]
        skip
      when T_487 :
        T_494[3] <= T_482[3]
        skip
      when T_488 :
        T_494[4] <= T_482[4]
        skip
      when T_489 :
        T_494[5] <= T_482[5]
        skip
      when T_490 :
        T_494[6] <= T_482[6]
        skip
      when T_491 :
        T_494[7] <= T_482[7]
        skip
      skip @[dcache.scala 33:39] 
    node T_497 = eq(io.req.bits.write, UInt<1>("h00")) @[dcache.scala 37:45] 
    node T_498 = and(T_467, T_497) @[dcache.scala 37:42] 
    wire T_500 : UInt
    T_500 is invalid
    when T_498 :
      T_500 <= addr
      skip
    read mport T_503 = T_463[T_500], clk
    node T_505 = cat(T_503[1], T_503[0]) @[dcache.scala 37:65] 
    node T_506 = cat(T_503[3], T_503[2]) @[dcache.scala 37:65] 
    node T_507 = cat(T_506, T_505) @[dcache.scala 37:65] 
    node T_508 = cat(T_503[5], T_503[4]) @[dcache.scala 37:65] 
    node T_509 = cat(T_503[7], T_503[6]) @[dcache.scala 37:65] 
    node T_510 = cat(T_509, T_508) @[dcache.scala 37:65] 
    node T_511 = cat(T_510, T_507) @[dcache.scala 37:65] 
    io.resp[1] <= T_511 @[dcache.scala 37:16] 
    smem T_520 : UInt<8>[8][512] @[dcache.scala 31:23] 
    node T_522 = bits(io.req.bits.way_en, 2, 2) @[dcache.scala 32:72] 
    node T_523 = or(UInt<1>("h00"), T_522) @[dcache.scala 32:51] 
    node T_524 = and(io.req.valid, T_523) @[dcache.scala 32:30] 
    node T_525 = and(T_524, io.req.bits.write) @[dcache.scala 33:17] 
    when T_525 : @[dcache.scala 33:39] 
      node T_526 = bits(io.req.bits.wdata, 7, 0) @[dcache.scala 34:63] 
      node T_527 = bits(io.req.bits.wdata, 15, 8) @[dcache.scala 34:63] 
      node T_528 = bits(io.req.bits.wdata, 23, 16) @[dcache.scala 34:63] 
      node T_529 = bits(io.req.bits.wdata, 31, 24) @[dcache.scala 34:63] 
      node T_530 = bits(io.req.bits.wdata, 39, 32) @[dcache.scala 34:63] 
      node T_531 = bits(io.req.bits.wdata, 47, 40) @[dcache.scala 34:63] 
      node T_532 = bits(io.req.bits.wdata, 55, 48) @[dcache.scala 34:63] 
      node T_533 = bits(io.req.bits.wdata, 63, 56) @[dcache.scala 34:63] 
      wire T_539 : UInt<8>[8] @[dcache.scala 34:40] 
      T_539 is invalid @[dcache.scala 34:40] 
      T_539[0] <= T_526 @[dcache.scala 34:40] 
      T_539[1] <= T_527 @[dcache.scala 34:40] 
      T_539[2] <= T_528 @[dcache.scala 34:40] 
      T_539[3] <= T_529 @[dcache.scala 34:40] 
      T_539[4] <= T_530 @[dcache.scala 34:40] 
      T_539[5] <= T_531 @[dcache.scala 34:40] 
      T_539[6] <= T_532 @[dcache.scala 34:40] 
      T_539[7] <= T_533 @[dcache.scala 34:40] 
      node T_541 = bits(io.req.bits.wmask, 0, 0) @[dcache.scala 35:49] 
      node T_542 = bits(io.req.bits.wmask, 1, 1) @[dcache.scala 35:49] 
      node T_543 = bits(io.req.bits.wmask, 2, 2) @[dcache.scala 35:49] 
      node T_544 = bits(io.req.bits.wmask, 3, 3) @[dcache.scala 35:49] 
      node T_545 = bits(io.req.bits.wmask, 4, 4) @[dcache.scala 35:49] 
      node T_546 = bits(io.req.bits.wmask, 5, 5) @[dcache.scala 35:49] 
      node T_547 = bits(io.req.bits.wmask, 6, 6) @[dcache.scala 35:49] 
      node T_548 = bits(io.req.bits.wmask, 7, 7) @[dcache.scala 35:49] 
      write mport T_551 = T_520[addr], clk
      when T_541 :
        T_551[0] <= T_539[0]
        skip
      when T_542 :
        T_551[1] <= T_539[1]
        skip
      when T_543 :
        T_551[2] <= T_539[2]
        skip
      when T_544 :
        T_551[3] <= T_539[3]
        skip
      when T_545 :
        T_551[4] <= T_539[4]
        skip
      when T_546 :
        T_551[5] <= T_539[5]
        skip
      when T_547 :
        T_551[6] <= T_539[6]
        skip
      when T_548 :
        T_551[7] <= T_539[7]
        skip
      skip @[dcache.scala 33:39] 
    node T_554 = eq(io.req.bits.write, UInt<1>("h00")) @[dcache.scala 37:45] 
    node T_555 = and(T_524, T_554) @[dcache.scala 37:42] 
    wire T_557 : UInt
    T_557 is invalid
    when T_555 :
      T_557 <= addr
      skip
    read mport T_560 = T_520[T_557], clk
    node T_562 = cat(T_560[1], T_560[0]) @[dcache.scala 37:65] 
    node T_563 = cat(T_560[3], T_560[2]) @[dcache.scala 37:65] 
    node T_564 = cat(T_563, T_562) @[dcache.scala 37:65] 
    node T_565 = cat(T_560[5], T_560[4]) @[dcache.scala 37:65] 
    node T_566 = cat(T_560[7], T_560[6]) @[dcache.scala 37:65] 
    node T_567 = cat(T_566, T_565) @[dcache.scala 37:65] 
    node T_568 = cat(T_567, T_564) @[dcache.scala 37:65] 
    io.resp[2] <= T_568 @[dcache.scala 37:16] 
    smem T_577 : UInt<8>[8][512] @[dcache.scala 31:23] 
    node T_579 = bits(io.req.bits.way_en, 3, 3) @[dcache.scala 32:72] 
    node T_580 = or(UInt<1>("h00"), T_579) @[dcache.scala 32:51] 
    node T_581 = and(io.req.valid, T_580) @[dcache.scala 32:30] 
    node T_582 = and(T_581, io.req.bits.write) @[dcache.scala 33:17] 
    when T_582 : @[dcache.scala 33:39] 
      node T_583 = bits(io.req.bits.wdata, 7, 0) @[dcache.scala 34:63] 
      node T_584 = bits(io.req.bits.wdata, 15, 8) @[dcache.scala 34:63] 
      node T_585 = bits(io.req.bits.wdata, 23, 16) @[dcache.scala 34:63] 
      node T_586 = bits(io.req.bits.wdata, 31, 24) @[dcache.scala 34:63] 
      node T_587 = bits(io.req.bits.wdata, 39, 32) @[dcache.scala 34:63] 
      node T_588 = bits(io.req.bits.wdata, 47, 40) @[dcache.scala 34:63] 
      node T_589 = bits(io.req.bits.wdata, 55, 48) @[dcache.scala 34:63] 
      node T_590 = bits(io.req.bits.wdata, 63, 56) @[dcache.scala 34:63] 
      wire T_596 : UInt<8>[8] @[dcache.scala 34:40] 
      T_596 is invalid @[dcache.scala 34:40] 
      T_596[0] <= T_583 @[dcache.scala 34:40] 
      T_596[1] <= T_584 @[dcache.scala 34:40] 
      T_596[2] <= T_585 @[dcache.scala 34:40] 
      T_596[3] <= T_586 @[dcache.scala 34:40] 
      T_596[4] <= T_587 @[dcache.scala 34:40] 
      T_596[5] <= T_588 @[dcache.scala 34:40] 
      T_596[6] <= T_589 @[dcache.scala 34:40] 
      T_596[7] <= T_590 @[dcache.scala 34:40] 
      node T_598 = bits(io.req.bits.wmask, 0, 0) @[dcache.scala 35:49] 
      node T_599 = bits(io.req.bits.wmask, 1, 1) @[dcache.scala 35:49] 
      node T_600 = bits(io.req.bits.wmask, 2, 2) @[dcache.scala 35:49] 
      node T_601 = bits(io.req.bits.wmask, 3, 3) @[dcache.scala 35:49] 
      node T_602 = bits(io.req.bits.wmask, 4, 4) @[dcache.scala 35:49] 
      node T_603 = bits(io.req.bits.wmask, 5, 5) @[dcache.scala 35:49] 
      node T_604 = bits(io.req.bits.wmask, 6, 6) @[dcache.scala 35:49] 
      node T_605 = bits(io.req.bits.wmask, 7, 7) @[dcache.scala 35:49] 
      write mport T_608 = T_577[addr], clk
      when T_598 :
        T_608[0] <= T_596[0]
        skip
      when T_599 :
        T_608[1] <= T_596[1]
        skip
      when T_600 :
        T_608[2] <= T_596[2]
        skip
      when T_601 :
        T_608[3] <= T_596[3]
        skip
      when T_602 :
        T_608[4] <= T_596[4]
        skip
      when T_603 :
        T_608[5] <= T_596[5]
        skip
      when T_604 :
        T_608[6] <= T_596[6]
        skip
      when T_605 :
        T_608[7] <= T_596[7]
        skip
      skip @[dcache.scala 33:39] 
    node T_611 = eq(io.req.bits.write, UInt<1>("h00")) @[dcache.scala 37:45] 
    node T_612 = and(T_581, T_611) @[dcache.scala 37:42] 
    wire T_614 : UInt
    T_614 is invalid
    when T_612 :
      T_614 <= addr
      skip
    read mport T_617 = T_577[T_614], clk
    node T_619 = cat(T_617[1], T_617[0]) @[dcache.scala 37:65] 
    node T_620 = cat(T_617[3], T_617[2]) @[dcache.scala 37:65] 
    node T_621 = cat(T_620, T_619) @[dcache.scala 37:65] 
    node T_622 = cat(T_617[5], T_617[4]) @[dcache.scala 37:65] 
    node T_623 = cat(T_617[7], T_617[6]) @[dcache.scala 37:65] 
    node T_624 = cat(T_623, T_622) @[dcache.scala 37:65] 
    node T_625 = cat(T_624, T_621) @[dcache.scala 37:65] 
    io.resp[3] <= T_625 @[dcache.scala 37:16] 
    