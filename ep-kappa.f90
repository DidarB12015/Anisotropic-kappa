
!
! Copyright (C) 2002-2004 Quantum ESPRESSO group
! This file is distributed under the terms of the
! GNU General Public License. See the file `License'
! in the root directory of the present distribution,
! or http://www.gnu.org/copyleft/gpl.txt .
!
!------------------------------------------------------------------------------!
    MODULE kinds
!------------------------------------------------------------------------------!

      IMPLICIT NONE
      SAVE
! ... kind definitions
      INTEGER, PARAMETER :: DP = selected_real_kind(14,200)
      INTEGER, PARAMETER :: sgl = selected_real_kind(6,30)
      INTEGER, PARAMETER :: i4b = selected_int_kind(9)
      PRIVATE
      PUBLIC :: i4b, sgl, DP
!
!------------------------------------------------------------------------------!
    END MODULE kinds
!------------------------------------------------------------------------------!

!
! Copyright (C) 2002-2006 Quantum ESPRESSO group
! This file is distributed under the terms of the
! GNU General Public License. See the file `License'
! in the root directory of the present distribution,
! or http://www.gnu.org/copyleft/gpl.txt .
!
!----------------------------------------------------------------------------
MODULE constants
  !----------------------------------------------------------------------------
  !
  USE kinds, ONLY : DP
  !
  ! ... The constants needed everywhere
  !
  IMPLICIT NONE
  !
  SAVE
  !
  ! ... Mathematical constants
  ! 
  REAL(DP), PARAMETER :: pi     = 3.14159265358979323846_DP 
  REAL(DP), PARAMETER :: tpi    = 2.0_DP * pi
  REAL(DP), PARAMETER :: fpi    = 4.0_DP * pi
  REAL(DP), PARAMETER :: sqrtpi = 1.77245385090551602729_DP 
  REAL(DP), PARAMETER :: sqrtpm1= 1.0_DP / sqrtpi
  REAL(DP), PARAMETER :: sqrt2  = 1.41421356237309504880_DP
  !
  ! ... Physical constants, SI (NIST CODATA 2006), Web Version 5.1
  !     http://physics.nist.gov/constants
  REAL(DP), PARAMETER :: H_PLANCK_SI      = 6.62606896E-34_DP   ! J s
  REAL(DP), PARAMETER :: K_BOLTZMANN_SI   = 1.3806504E-23_DP    ! J K^-1 
  REAL(DP), PARAMETER :: ELECTRON_SI      = 1.602176487E-19_DP  ! C
  REAL(DP), PARAMETER :: ELECTRONVOLT_SI  = 1.602176487E-19_DP  ! J  
  REAL(DP), PARAMETER :: ELECTRONMASS_SI  = 9.10938215E-31_DP   ! Kg
  REAL(DP), PARAMETER :: HARTREE_SI       = 4.35974394E-18_DP   ! J
  REAL(DP), PARAMETER :: RYDBERG_SI       = HARTREE_SI/2.0_DP   ! J
  REAL(DP), PARAMETER :: BOHR_RADIUS_SI   = 0.52917720859E-10_DP ! m
  REAL(DP), PARAMETER :: AMU_SI           = 1.660538782E-27_DP  ! Kg
  REAL(DP), PARAMETER :: C_SI             = 2.99792458E+8_DP    ! m sec^-1
  REAL(DP), PARAMETER :: MUNOUGHT_SI      = fpi*1.0E-7_DP       ! N A^-2
  REAL(DP), PARAMETER :: EPSNOUGHT_SI     = 1.0_DP / (MUNOUGHT_SI * &
                                                       C_SI**2) ! F m^-1
  !
  ! ... Physical constants, atomic units:
  ! ... AU for "Hartree" atomic units (e = m = hbar = 1)
  ! ... RY for "Rydberg" atomic units (e^2=2, m=1/2, hbar=1)
  !
  REAL(DP), PARAMETER :: K_BOLTZMANN_AU   = K_BOLTZMANN_SI / HARTREE_SI
  REAL(DP), PARAMETER :: K_BOLTZMANN_RY   = K_BOLTZMANN_SI / RYDBERG_SI
  !
  ! ... Unit conversion factors: energy and masses
  !
  REAL(DP), PARAMETER :: AUTOEV           = HARTREE_SI / ELECTRONVOLT_SI
  REAL(DP), PARAMETER :: RYTOEV           = AUTOEV / 2.0_DP
  REAL(DP), PARAMETER :: AMU_AU           = AMU_SI / ELECTRONMASS_SI
  REAL(DP), PARAMETER :: AMU_RY           = AMU_AU / 2.0_DP
  !
  ! ... Unit conversion factors: atomic unit of time, in s and ps
  !
  REAL(DP), PARAMETER :: AU_SEC           = H_PLANCK_SI/tpi/HARTREE_SI
  REAL(DP), PARAMETER :: AU_PS            = AU_SEC * 1.0E+12_DP
  !
  ! ... Unit conversion factors: pressure (1 Pa = 1 J/m^3, 1GPa = 10 Kbar )
  !
  REAL(DP), PARAMETER :: AU_GPA           = HARTREE_SI / BOHR_RADIUS_SI ** 3 &
                                            / 1.0E+9_DP 
  REAL(DP), PARAMETER :: RY_KBAR          = 10.0_DP * AU_GPA / 2.0_DP
  !
  ! ... Unit conversion factors: 1 debye = 10^-18 esu*cm 
  ! ...                                  = 3.3356409519*10^-30 C*m 
  ! ...                                  = 0.208194346 e*A
  ! ... ( 1 esu = (0.1/c) Am, c=299792458 m/s)
  !
  REAL(DP), PARAMETER :: DEBYE_SI         = 3.3356409519_DP * 1.0E-30_DP ! C*m 
  REAL(DP), PARAMETER :: AU_DEBYE         = ELECTRON_SI * BOHR_RADIUS_SI / &
                                            DEBYE_SI
  !
  REAL(DP), PARAMETER :: eV_to_kelvin = ELECTRONVOLT_SI / K_BOLTZMANN_SI
  REAL(DP), PARAMETER :: ry_to_kelvin = RYDBERG_SI / K_BOLTZMANN_SI
  !
  ! .. Unit conversion factors: Energy to wavelength
  !
  REAL(DP), PARAMETER :: EVTONM = 1E+9_DP * H_PLANCK_SI * C_SI / &
                                  &ELECTRONVOLT_SI
  REAL(DP), PARAMETER :: RYTONM = 1E+9_DP * H_PLANCK_SI * C_SI / RYDBERG_SI
  !
  !  Speed of light in atomic units
  !
  REAL(DP), PARAMETER :: C_AU             = C_SI / BOHR_RADIUS_SI * AU_SEC
  !
  ! ... zero up to a given accuracy
  !
  REAL(DP), PARAMETER :: eps4  = 1.0E-4_DP
  REAL(DP), PARAMETER :: eps6  = 1.0E-6_DP
  REAL(DP), PARAMETER :: eps8  = 1.0E-8_DP
  REAL(DP), PARAMETER :: eps12 = 1.0E-12_DP
  REAL(DP), PARAMETER :: eps14 = 1.0E-14_DP
  REAL(DP), PARAMETER :: eps16 = 1.0E-16_DP
  REAL(DP), PARAMETER :: eps24 = 1.0E-24_DP
  REAL(DP), PARAMETER :: eps32 = 1.0E-32_DP
  !
  REAL(DP), PARAMETER :: gsmall = 1.0E-12_DP
  !
  REAL(DP), PARAMETER :: e2 = 2.0_DP      ! the square of the electron charge
  REAL(DP), PARAMETER :: degspin = 2.0_DP ! the number of spins per level
  !
  !!!!!! COMPATIBIILITY
  !
  REAL(DP), PARAMETER :: BOHR_RADIUS_CM = BOHR_RADIUS_SI * 100.0_DP
  REAL(DP), PARAMETER :: BOHR_RADIUS_ANGS = BOHR_RADIUS_CM * 1.0E8_DP
  REAL(DP), PARAMETER :: ANGSTROM_AU = 1.0_DP/BOHR_RADIUS_ANGS
  REAL(DP), PARAMETER :: DIP_DEBYE = AU_DEBYE
  REAL(DP), PARAMETER :: AU_TERAHERTZ  = AU_PS
  REAL(DP), PARAMETER :: AU_TO_OHMCMM1 = 46000.0_DP ! (ohm cm)^-1
  REAL(DP), PARAMETER :: RY_TO_THZ = 1.0_DP / AU_TERAHERTZ / FPI
  REAL(DP), PARAMETER :: RY_TO_GHZ = RY_TO_THZ*1000.0_DP
  REAL(DP), PARAMETER :: RY_TO_CMM1 = 1.E+10_DP * RY_TO_THZ / C_SI
  !

END MODULE constants

!
! Copyright (C) 2001-2003 PWSCF group
! This file is distributed under the terms of the
! GNU General Public License. See the file `License'
! in the root directory of the present distribution,
! or http://www.gnu.org/copyleft/gpl.txt .
!
!-----------------------------------------------------------------------
subroutine cryst_to_cart (nvec, vec, trmat, iflag)
  !-----------------------------------------------------------------------
  !
  !     This routine transforms the atomic positions or the k-point
  !     components from crystallographic to cartesian coordinates 
  !     ( iflag=1 ) and viceversa ( iflag=-1 ).
  !     Output cartesian coordinates are stored in the input ('vec') array
  !
  !
  USE kinds, ONLY : DP
  implicit none
  !
  integer, intent(in) :: nvec, iflag
  ! nvec:  number of vectors (atomic positions or k-points)
  !        to be transformed from crystal to cartesian and vice versa
  ! iflag: gives the direction of the transformation
  real(DP), intent(in) :: trmat (3, 3)
  ! trmat: transformation matrix
  ! if iflag=1:
  !    trmat = at ,  basis of the real-space lattice,       for atoms   or
  !          = bg ,  basis of the reciprocal-space lattice, for k-points
  ! if iflag=-1: the opposite
  real(DP), intent(inout) :: vec (3, nvec)
  ! coordinates of the vector (atomic positions or k-points) to be
  ! transformed - overwritten on output
  !
  !    local variables
  !
  integer :: nv, kpol
  ! counter on vectors
  ! counter on polarizations
  real(DP) :: vau (3)
  ! workspace
  !
  !     Compute the cartesian coordinates of each vectors
  !     (atomic positions or k-points components)
  !
  do nv = 1, nvec
     if (iflag.eq.1) then
        do kpol = 1, 3
           vau (kpol) = trmat (kpol, 1) * vec (1, nv) + trmat (kpol, 2) &
                * vec (2, nv) + trmat (kpol, 3) * vec (3, nv)
        enddo
     else
        do kpol = 1, 3
           vau (kpol) = trmat (1, kpol) * vec (1, nv) + trmat (2, kpol) &
                * vec (2, nv) + trmat (3, kpol) * vec (3, nv)
        enddo
     endif
     do kpol = 1, 3
        vec (kpol, nv) = vau (kpol)
     enddo
  enddo
  !
  return
end subroutine cryst_to_cart

!
! Copyright (C) 2012 Quantum ESPRESSO group
! This file is distributed under the terms of the
! GNU General Public License. See the file `License'
! in the root directory of the present distribution,
! or http://www.gnu.org/copyleft/gpl.txt .
!
!----------------------------------------------------------------------
SUBROUTINE dyn_pattern_to_cart(nat, u, dyn, phi)
! This routine transforms the dynamical matrix dyn, written in the basis
! of the pattern, in the dynamical matrix phi, in the cartesian basis.
  USE kinds, ONLY : DP
  IMPLICIT NONE
  INTEGER, INTENT(IN) :: nat
  COMPLEX(DP), INTENT(IN) :: u(3*nat, 3*nat)
  COMPLEX(DP), INTENT(IN) :: dyn(3*nat, 3*nat)
  COMPLEX(DP), INTENT(OUT) :: phi(3, 3, nat, nat)

  COMPLEX(DP) :: work
  INTEGER :: i, j, icart, jcart, na, nb, mu, nu

  DO i = 1, 3 * nat
     na = (i - 1) / 3 + 1
     icart = i - 3 * (na - 1)
     DO j = 1, 3 * nat
        nb = (j - 1) / 3 + 1
        jcart = j - 3 * (nb - 1)
        work = (0.d0, 0.d0)
        DO mu = 1, 3 * nat
           DO nu = 1, 3 * nat
              work = work + u (i, mu) * dyn (mu, nu) * CONJG(u (j, nu) )
           ENDDO
        ENDDO
        phi (icart, jcart, na, nb) = work
     ENDDO
  ENDDO

  RETURN 
END SUBROUTINE dyn_pattern_to_cart
!
!-----------------------------------------------------------------------
SUBROUTINE compact_dyn(nat, dyn, phi)
!-----------------------------------------------------------------------
!
!  This routine writes the dynamical matrix from a 3,3,nat,nat array
!  to a 3*nat,3*nat array. 
!
  USE kinds, ONLY : DP
  IMPLICIT NONE
  INTEGER, INTENT(IN) :: nat
  COMPLEX(DP), INTENT(IN) :: phi(3,3,nat,nat)
  COMPLEX(DP), INTENT(OUT) :: dyn(3*nat, 3*nat)

  INTEGER :: na, nb, icart, jcart, imode, jmode

  DO na = 1, nat
     DO icart = 1, 3
        imode = 3 * ( na - 1 ) + icart
        DO nb = 1, nat
           DO jcart = 1, 3
              jmode = 3 * ( nb - 1 ) + jcart
              dyn (imode, jmode) = phi (icart, jcart, na, nb)
           END DO 
        END DO
     END DO
  END DO
  RETURN
  END SUBROUTINE compact_dyn

!
! Copyright (C) 2001 PWSCF group
! This file is distributed under the terms of the
! GNU General Public License. See the file `License'
! in the root directory of the present distribution,
! or http://www.gnu.org/copyleft/gpl.txt .
!
!
!-----------------------------------------------------------------------
subroutine trntnsc (phi, at, bg, iflg)
  !-----------------------------------------------------------------------
  !
  ! trasforms a COMPLEX tensor (like the dynamical matrix)
  ! from crystal to cartesian axis (iflg >=  1) or viceversa (iflg <= -1)
  !
  USE kinds, only : DP
  implicit none

  integer :: iflg
  ! input: gives the versus of the trans.

  complex(DP) :: phi (3, 3)
  ! inp/out: the matrix to transform

  real(DP) :: at (3, 3), bg (3, 3)
  ! input: the direct lattice vectors
  ! input: the reciprocal lattice

  integer :: i, j, k, l
  !
  !  counters on polarizations
  ! /
  !/

  complex(DP) :: wrk (3, 3)
  ! a working array
  if (iflg.gt.0) then
     !
     ! forward transformation (crystal to cartesian axis)
     !

     call zcopy (9, phi, 1, wrk, 1)
     do i = 1, 3
        do j = 1, 3
           phi (i, j) = (0.d0, 0.d0)
           do k = 1, 3
              do l = 1, 3
                 phi (i, j) = phi (i, j) + wrk (k, l) * bg (i, k) * bg (j, l)
              enddo
           enddo
        enddo
     enddo
  else
     !
     ! backward transformation (cartesian to crystal axis)
     !
     do i = 1, 3
        do j = 1, 3
           wrk (i, j) = (0.d0, 0.d0)
           do k = 1, 3
              do l = 1, 3
                 wrk (i, j) = wrk (i, j) + phi (k, l) * at (k, i) * at (l, j)
              enddo
           enddo
        enddo
     enddo
     call zcopy (9, wrk, 1, phi, 1)
  endif
  return
end subroutine trntnsc

!
! Copyright (C) 2001-2012 Quantum ESPRESSO group
! This file is distributed under the terms of the
! GNU General Public License. See the file `License'
! in the root directory of the present distribution,
! or http://www.gnu.org/copyleft/gpl.txt .
!
!-----------------------------------------------------------------------
subroutine symdynph_gq_new (xq, phi, s, invs, rtau, irt, nsymq, &
     nat, irotmq, minus_q)
  !-----------------------------------------------------------------------
  !
  !     This routine receives as input an unsymmetrized dynamical
  !     matrix expressed on the crystal axes and imposes the symmetry
  !     of the small group of q. Furthermore it imposes also the symmetry
  !     q -> -q+G if present.
  !
  !
  USE kinds, only : DP
  USE constants, ONLY: tpi
  implicit none
  !
  !    The dummy variables
  !
  integer :: nat, s (3, 3, 48), irt (48, nat), invs (48), &
       nsymq, irotmq
  ! input: the number of atoms
  ! input: the symmetry matrices
  ! input: the rotated of each vector
  ! input: the small group of q
  ! input: the inverse of each matrix
  ! input: the order of the small gro
  ! input: the rotation sending q ->
  real(DP) :: xq (3), rtau (3, 48, nat)
  ! input: the q point
  ! input: the R associated at each t

  logical :: minus_q
  ! input: true if a symmetry q->-q+G
  complex(DP) :: phi (3, 3, nat, nat)
  ! inp/out: the matrix to symmetrize
  !
  !   local variables
  !
  integer :: isymq, sna, snb, irot, na, nb, ipol, jpol, lpol, kpol, &
       iflb (nat, nat)
  ! counters, indices, work space

  real(DP) :: arg
  ! the argument of the phase

  complex(DP) :: phip (3, 3, nat, nat), work (3, 3), fase, faseq (48)
  ! work space, phase factors
  !
  !    We start by imposing hermiticity
  !
  do na = 1, nat
     do nb = 1, nat
        do ipol = 1, 3
           do jpol = 1, 3
              phi (ipol, jpol, na, nb) = 0.5d0 * (phi (ipol, jpol, na, nb) &
                   + CONJG(phi (jpol, ipol, nb, na) ) )
              phi (jpol, ipol, nb, na) = CONJG(phi (ipol, jpol, na, nb) )
           enddo
        enddo
     enddo
  enddo
  !
  !    If no other symmetry is present we quit here
  !
  if ( (nsymq == 1) .and. (.not.minus_q) ) return
  !
  !    Then we impose the symmetry q -> -q+G if present
  !
  if (minus_q) then
     do na = 1, nat
        do nb = 1, nat
           do ipol = 1, 3
              do jpol = 1, 3
                 work(:,:) = (0.d0, 0.d0)
                 sna = irt (irotmq, na)
                 snb = irt (irotmq, nb)
                 arg = 0.d0
                 do kpol = 1, 3
                    arg = arg + (xq (kpol) * (rtau (kpol, irotmq, na) - &
                                              rtau (kpol, irotmq, nb) ) )
                 enddo
                 arg = arg * tpi
                 fase = CMPLX(cos (arg), sin (arg) ,kind=DP)
                 do kpol = 1, 3
                    do lpol = 1, 3
                       work (ipol, jpol) = work (ipol, jpol) + &
                            s (ipol, kpol, irotmq) * s (jpol, lpol, irotmq) &
                            * phi (kpol, lpol, sna, snb) * fase
                    enddo
                 enddo
                 phip (ipol, jpol, na, nb) = (phi (ipol, jpol, na, nb) + &
                      CONJG( work (ipol, jpol) ) ) * 0.5d0
              enddo
           enddo
        enddo
     enddo
     phi = phip
  endif

  !
  !    Here we symmetrize with respect to the small group of q
  !
  if (nsymq == 1) return

  iflb (:, :) = 0
  do na = 1, nat
     do nb = 1, nat
        if (iflb (na, nb) == 0) then
           work(:,:) = (0.d0, 0.d0)
           do isymq = 1, nsymq
              irot = isymq
              sna = irt (irot, na)
              snb = irt (irot, nb)
              arg = 0.d0
              do ipol = 1, 3
                 arg = arg + (xq (ipol) * (rtau (ipol, irot, na) - &
                                           rtau (ipol, irot, nb) ) )
              enddo
              arg = arg * tpi
              faseq (isymq) = CMPLX(cos (arg), sin (arg) ,kind=DP)
              do ipol = 1, 3
                 do jpol = 1, 3
                    do kpol = 1, 3
                       do lpol = 1, 3
                          work (ipol, jpol) = work (ipol, jpol) + &
                               s (ipol, kpol, irot) * s (jpol, lpol, irot) &
                               * phi (kpol, lpol, sna, snb) * faseq (isymq)
                       enddo
                    enddo
                 enddo
              enddo
           enddo
           do isymq = 1, nsymq
              irot = isymq
              sna = irt (irot, na)
              snb = irt (irot, nb)
              do ipol = 1, 3
                 do jpol = 1, 3
                    phi (ipol, jpol, sna, snb) = (0.d0, 0.d0)
                    do kpol = 1, 3
                       do lpol = 1, 3
                          phi (ipol, jpol, sna, snb) = phi (ipol, jpol, sna, snb) &
                               + s (ipol, kpol, invs (irot) ) * s (jpol, lpol, invs (irot) ) &
                               * work (kpol, lpol) * CONJG(faseq (isymq) )
                       enddo
                    enddo
                 enddo
              enddo
              iflb (sna, snb) = 1
           enddo
        endif
     enddo
  enddo
  phi (:, :, :, :) = phi (:, :, :, :) / DBLE(nsymq)
  return
end subroutine symdynph_gq_new

!
! Copyright (C) 2001-2012 PWSCF group
! This file is distributed under the terms of the
! GNU General Public License. See the file `License'
! in the root directory of the present distribution,
! or http://www.gnu.org/copyleft/gpl.txt .
!
!-----------------------------------------------------------------------
subroutine symdyn_munu_new (dyn, u, xq, s, invs, rtau, irt, at, &
     bg, nsymq, nat, irotmq, minus_q)
  !-----------------------------------------------------------------------
  !
  !    This routine symmetrize the dynamical matrix written in the basis
  !    of the modes
  !
  !
  USE kinds, only : DP
  implicit none
  integer :: nat, s (3, 3, 48), irt (48, nat), invs (48), &
       nsymq, irotmq
  ! input: the number of atoms
  ! input: the symmetry matrices
  ! input: the rotated of each atom
  ! input: the small group of q
  ! input: the inverse of each matrix
  ! input: the order of the small gro
  ! input: the symmetry q -> -q+G

  real(DP) :: xq (3), rtau (3, 48, nat), at (3, 3), bg (3, 3)
  ! input: the coordinates of q
  ! input: the R associated at each r
  ! input: direct lattice vectors
  ! input: reciprocal lattice vectors

  logical :: minus_q
  ! input: if true symmetry sends q->

  complex(DP) :: dyn (3 * nat, 3 * nat), u (3 * nat, 3 * nat)
  ! inp/out: matrix to symmetrize
  ! input: the patterns

  integer :: i, j, icart, jcart, na, nb, mu, nu
  ! counter on modes
  ! counter on modes
  ! counter on cartesian coordinates
  ! counter on cartesian coordinates
  ! counter on atoms
  ! counter on atoms
  ! counter on modes
  ! counter on modes

  complex(DP) :: work, phi (3, 3, nat, nat)
  ! auxiliary variable
  ! the dynamical matrix
  !
  ! First we transform in the cartesian coordinates
  !
  CALL dyn_pattern_to_cart(nat, u, dyn, phi)
  !
  ! Then we transform to the crystal axis
  !
  do na = 1, nat
     do nb = 1, nat
        call trntnsc (phi (1, 1, na, nb), at, bg, - 1)
     enddo
  enddo
  !
  !   And we symmetrize in this basis
  !
  call symdynph_gq_new (xq, phi, s, invs, rtau, irt, nsymq, nat, &
       irotmq, minus_q)
  !
  !  Back to cartesian coordinates
  !
  do na = 1, nat
     do nb = 1, nat
        call trntnsc (phi (1, 1, na, nb), at, bg, + 1)
     enddo
  enddo
  !
  !  rewrite the dynamical matrix on the array dyn with dimension 3nat x 3nat
  !
  CALL compact_dyn(nat, dyn, phi)

  return
end subroutine symdyn_munu_new

