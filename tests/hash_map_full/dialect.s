    #$ ctrl thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    #$ keys thread [u32 u32 u32 u32 u32 u32 u32 u32]
    #$ vals thread [u32 u32 u32 u32 u32 u32 u32 u32]
    li a6, 8
    bnez a6, _l0
    #!
_l0:
    li t2, 8
    rem t1, a6, t2
    beqz t1, _l1
    #!
_l1:
    li t3, 2
    li t2, 1
    addi t1, a6, 0
_l2:
    beq t1, t2, _l3
    rem t0, t1, t3
    beqz t0, _l4
    #!
_l4:
    div t1, t1, t3
    j _l2
_l3:
    li t2, 128
    addi t1, a6, 8
    la t0, ctrl
_l5:
    beqz t1, _l6
    #] t2, 0(t0)
    addi t0, t0, 1
    addi t1, t1, -1
    j _l5
_l6:
    li a0, 1
    li a1, 10
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l7:
    beqz t5, _l8
    li t4, 0
_l9:
    bge t4, a4, _l10
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    bne t1, t2, _l11
    addi a3, a6, 0
_l11:
    bne t1, t3, _l12
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #[ t0, 0(t0)
    bne t0, a0, _l13
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l13:
_l12:
    addi t4, t4, 1
    j _l9
_l10:
    beqz t5, _l14
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l15
    addi a2, a6, 0
    li t5, 0
_l15:
_l14:
    j _l7
_l8:
    addi a5, a2, 0
    bne a5, a6, _l16
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l17:
    beqz t5, _l18
    li t4, 0
_l19:
    bge t4, a4, _l20
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    blt t1, t2, _l21
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l21:
    addi t4, t4, 1
    j _l19
_l20:
    beqz t5, _l22
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l23
    addi a2, a6, 0
    li t5, 0
_l23:
_l22:
    j _l17
_l18:
    addi a5, a2, 0
    bne a5, a6, _l24
    #!
_l24:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    #] t3, 0(t0)
    li a4, 8
    bge a5, a4, _l25
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    #] t3, 0(t0)
_l25:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #] a0, 0(t0)
_l16:
    la t0, vals
    add t0, t0, t1
    #] a1, 0(t0)
    addi a5, a5, 0
    li a0, 2
    li a1, 20
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l26:
    beqz t5, _l27
    li t4, 0
_l28:
    bge t4, a4, _l29
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    bne t1, t2, _l30
    addi a3, a6, 0
_l30:
    bne t1, t3, _l31
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #[ t0, 0(t0)
    bne t0, a0, _l32
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l32:
_l31:
    addi t4, t4, 1
    j _l28
_l29:
    beqz t5, _l33
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l34
    addi a2, a6, 0
    li t5, 0
_l34:
_l33:
    j _l26
_l27:
    addi a5, a2, 0
    bne a5, a6, _l35
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l36:
    beqz t5, _l37
    li t4, 0
_l38:
    bge t4, a4, _l39
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    blt t1, t2, _l40
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l40:
    addi t4, t4, 1
    j _l38
_l39:
    beqz t5, _l41
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l42
    addi a2, a6, 0
    li t5, 0
_l42:
_l41:
    j _l36
_l37:
    addi a5, a2, 0
    bne a5, a6, _l43
    #!
_l43:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    #] t3, 0(t0)
    li a4, 8
    bge a5, a4, _l44
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    #] t3, 0(t0)
_l44:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #] a0, 0(t0)
_l35:
    la t0, vals
    add t0, t0, t1
    #] a1, 0(t0)
    addi a5, a5, 0
    li a0, 3
    li a1, 30
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l45:
    beqz t5, _l46
    li t4, 0
_l47:
    bge t4, a4, _l48
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    bne t1, t2, _l49
    addi a3, a6, 0
_l49:
    bne t1, t3, _l50
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #[ t0, 0(t0)
    bne t0, a0, _l51
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l51:
_l50:
    addi t4, t4, 1
    j _l47
_l48:
    beqz t5, _l52
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l53
    addi a2, a6, 0
    li t5, 0
_l53:
_l52:
    j _l45
_l46:
    addi a5, a2, 0
    bne a5, a6, _l54
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l55:
    beqz t5, _l56
    li t4, 0
_l57:
    bge t4, a4, _l58
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    blt t1, t2, _l59
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l59:
    addi t4, t4, 1
    j _l57
_l58:
    beqz t5, _l60
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l61
    addi a2, a6, 0
    li t5, 0
_l61:
_l60:
    j _l55
_l56:
    addi a5, a2, 0
    bne a5, a6, _l62
    #!
_l62:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    #] t3, 0(t0)
    li a4, 8
    bge a5, a4, _l63
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    #] t3, 0(t0)
_l63:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #] a0, 0(t0)
_l54:
    la t0, vals
    add t0, t0, t1
    #] a1, 0(t0)
    addi a5, a5, 0
    li a0, 4
    li a1, 40
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l64:
    beqz t5, _l65
    li t4, 0
_l66:
    bge t4, a4, _l67
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    bne t1, t2, _l68
    addi a3, a6, 0
_l68:
    bne t1, t3, _l69
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #[ t0, 0(t0)
    bne t0, a0, _l70
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l70:
_l69:
    addi t4, t4, 1
    j _l66
_l67:
    beqz t5, _l71
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l72
    addi a2, a6, 0
    li t5, 0
_l72:
_l71:
    j _l64
_l65:
    addi a5, a2, 0
    bne a5, a6, _l73
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l74:
    beqz t5, _l75
    li t4, 0
_l76:
    bge t4, a4, _l77
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    blt t1, t2, _l78
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l78:
    addi t4, t4, 1
    j _l76
_l77:
    beqz t5, _l79
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l80
    addi a2, a6, 0
    li t5, 0
_l80:
_l79:
    j _l74
_l75:
    addi a5, a2, 0
    bne a5, a6, _l81
    #!
_l81:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    #] t3, 0(t0)
    li a4, 8
    bge a5, a4, _l82
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    #] t3, 0(t0)
_l82:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #] a0, 0(t0)
_l73:
    la t0, vals
    add t0, t0, t1
    #] a1, 0(t0)
    addi a5, a5, 0
    li a0, 5
    li a1, 50
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l83:
    beqz t5, _l84
    li t4, 0
_l85:
    bge t4, a4, _l86
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    bne t1, t2, _l87
    addi a3, a6, 0
_l87:
    bne t1, t3, _l88
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #[ t0, 0(t0)
    bne t0, a0, _l89
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l89:
_l88:
    addi t4, t4, 1
    j _l85
_l86:
    beqz t5, _l90
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l91
    addi a2, a6, 0
    li t5, 0
_l91:
_l90:
    j _l83
_l84:
    addi a5, a2, 0
    bne a5, a6, _l92
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l93:
    beqz t5, _l94
    li t4, 0
_l95:
    bge t4, a4, _l96
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    blt t1, t2, _l97
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l97:
    addi t4, t4, 1
    j _l95
_l96:
    beqz t5, _l98
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l99
    addi a2, a6, 0
    li t5, 0
_l99:
_l98:
    j _l93
_l94:
    addi a5, a2, 0
    bne a5, a6, _l100
    #!
_l100:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    #] t3, 0(t0)
    li a4, 8
    bge a5, a4, _l101
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    #] t3, 0(t0)
_l101:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #] a0, 0(t0)
_l92:
    la t0, vals
    add t0, t0, t1
    #] a1, 0(t0)
    addi a5, a5, 0
    li a0, 6
    li a1, 60
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l102:
    beqz t5, _l103
    li t4, 0
_l104:
    bge t4, a4, _l105
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    bne t1, t2, _l106
    addi a3, a6, 0
_l106:
    bne t1, t3, _l107
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #[ t0, 0(t0)
    bne t0, a0, _l108
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l108:
_l107:
    addi t4, t4, 1
    j _l104
_l105:
    beqz t5, _l109
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l110
    addi a2, a6, 0
    li t5, 0
_l110:
_l109:
    j _l102
_l103:
    addi a5, a2, 0
    bne a5, a6, _l111
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l112:
    beqz t5, _l113
    li t4, 0
_l114:
    bge t4, a4, _l115
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    blt t1, t2, _l116
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l116:
    addi t4, t4, 1
    j _l114
_l115:
    beqz t5, _l117
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l118
    addi a2, a6, 0
    li t5, 0
_l118:
_l117:
    j _l112
_l113:
    addi a5, a2, 0
    bne a5, a6, _l119
    #!
_l119:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    #] t3, 0(t0)
    li a4, 8
    bge a5, a4, _l120
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    #] t3, 0(t0)
_l120:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #] a0, 0(t0)
_l111:
    la t0, vals
    add t0, t0, t1
    #] a1, 0(t0)
    addi a5, a5, 0
    li a0, 7
    li a1, 70
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l121:
    beqz t5, _l122
    li t4, 0
_l123:
    bge t4, a4, _l124
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    bne t1, t2, _l125
    addi a3, a6, 0
_l125:
    bne t1, t3, _l126
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #[ t0, 0(t0)
    bne t0, a0, _l127
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l127:
_l126:
    addi t4, t4, 1
    j _l123
_l124:
    beqz t5, _l128
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l129
    addi a2, a6, 0
    li t5, 0
_l129:
_l128:
    j _l121
_l122:
    addi a5, a2, 0
    bne a5, a6, _l130
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l131:
    beqz t5, _l132
    li t4, 0
_l133:
    bge t4, a4, _l134
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    blt t1, t2, _l135
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l135:
    addi t4, t4, 1
    j _l133
_l134:
    beqz t5, _l136
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l137
    addi a2, a6, 0
    li t5, 0
_l137:
_l136:
    j _l131
_l132:
    addi a5, a2, 0
    bne a5, a6, _l138
    #!
_l138:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    #] t3, 0(t0)
    li a4, 8
    bge a5, a4, _l139
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    #] t3, 0(t0)
_l139:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #] a0, 0(t0)
_l130:
    la t0, vals
    add t0, t0, t1
    #] a1, 0(t0)
    addi a5, a5, 0
    li a0, 8
    li a1, 80
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l140:
    beqz t5, _l141
    li t4, 0
_l142:
    bge t4, a4, _l143
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    bne t1, t2, _l144
    addi a3, a6, 0
_l144:
    bne t1, t3, _l145
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #[ t0, 0(t0)
    bne t0, a0, _l146
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l146:
_l145:
    addi t4, t4, 1
    j _l142
_l143:
    beqz t5, _l147
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l148
    addi a2, a6, 0
    li t5, 0
_l148:
_l147:
    j _l140
_l141:
    addi a5, a2, 0
    bne a5, a6, _l149
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l150:
    beqz t5, _l151
    li t4, 0
_l152:
    bge t4, a4, _l153
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    blt t1, t2, _l154
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l154:
    addi t4, t4, 1
    j _l152
_l153:
    beqz t5, _l155
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l156
    addi a2, a6, 0
    li t5, 0
_l156:
_l155:
    j _l150
_l151:
    addi a5, a2, 0
    bne a5, a6, _l157
    #!
_l157:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    #] t3, 0(t0)
    li a4, 8
    bge a5, a4, _l158
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    #] t3, 0(t0)
_l158:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #] a0, 0(t0)
_l149:
    la t0, vals
    add t0, t0, t1
    #] a1, 0(t0)
    addi a5, a5, 0
    li a0, 9
    li a1, 90
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l159:
    beqz t5, _l160
    li t4, 0
_l161:
    bge t4, a4, _l162
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    bne t1, t2, _l163
    addi a3, a6, 0
_l163:
    bne t1, t3, _l164
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #[ t0, 0(t0)
    bne t0, a0, _l165
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l165:
_l164:
    addi t4, t4, 1
    j _l161
_l162:
    beqz t5, _l166
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l167
    addi a2, a6, 0
    li t5, 0
_l167:
_l166:
    j _l159
_l160:
    addi a5, a2, 0
    bne a5, a6, _l168
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l169:
    beqz t5, _l170
    li t4, 0
_l171:
    bge t4, a4, _l172
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    #[ t1, 0(t0)
    blt t1, t2, _l173
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l173:
    addi t4, t4, 1
    j _l171
_l172:
    beqz t5, _l174
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l175
    addi a2, a6, 0
    li t5, 0
_l175:
_l174:
    j _l169
_l170:
    addi a5, a2, 0
    bne a5, a6, _l176
    #!
_l176:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    #] t3, 0(t0)
    li a4, 8
    bge a5, a4, _l177
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    #] t3, 0(t0)
_l177:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    #] a0, 0(t0)
_l168:
    la t0, vals
    add t0, t0, t1
    #] a1, 0(t0)
    addi a5, a5, 0
    li a0, 0
    li a7, 93
    ecall
    #?
