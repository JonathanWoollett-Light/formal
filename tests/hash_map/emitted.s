.global _start
_start:
    #$ ctrl thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    #$ keys thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    #$ vals thread [u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32 u32]
    li a6, 16
    bnez a6, _l0
_l0:
    li t2, 8
    rem t1, a6, t2
    beqz t1, _l1
_l1:
    li t3, 2
    li t2, 1
    addi t1, a6, 0
_l2:
    beq t1, t2, _l3
    rem t0, t1, t3
    beqz t0, _l4
_l4:
    div t1, t1, t3
    j _l2
_l3:
    li t2, 128
    addi t1, a6, 8
    la t0, ctrl
_l5:
    beqz t1, _l6
    sb t2, 0(t0)  # #] t2, 0(t0)
    addi t0, t0, 1
    addi t1, t1, -1
    j _l5
_l6:
    li a0, 1
    li a1, 100
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
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    addi a3, a6, 0
_l11:
    bne t1, t3, _l12
_l12:
    addi t4, t4, 1
    j _l9
_l10:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    addi a2, a6, 0
    li t5, 0
_l15:
_l14:
    j _l7
_l8:
    addi a5, a2, 0
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
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l21:
    addi t4, t4, 1
    j _l19
_l20:
    beqz t5, _l22
_l22:
    j _l17
_l18:
    addi a5, a2, 0
    bne a5, a6, _l24
_l24:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    sb t3, 0(t0)  # #] t3, 0(t0)
    li a4, 8
    bge a5, a4, _l25
_l25:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    sw a0, 0(t0)  # #] a0, 0(t0)
_l16:
    la t0, vals
    add t0, t0, t1
    sw a1, 0(t0)  # #] a1, 0(t0)
    addi a5, a5, 0
    li t0, 12
    beq a5, t0, _l26
_l26:
    li a0, 10
    li a1, 110
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l27:
    beqz t5, _l28
    li t4, 0
_l29:
    bge t4, a4, _l30
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l31
    addi a3, a6, 0
_l31:
    bne t1, t3, _l32
_l32:
    addi t4, t4, 1
    j _l29
_l30:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    addi a2, a6, 0
    li t5, 0
_l35:
_l34:
    j _l27
_l28:
    addi a5, a2, 0
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l37:
    beqz t5, _l38
    li t4, 0
_l39:
    bge t4, a4, _l40
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    blt t1, t2, _l41
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l41:
    addi t4, t4, 1
    j _l39
_l40:
    beqz t5, _l42
_l42:
    j _l37
_l38:
    addi a5, a2, 0
    bne a5, a6, _l44
_l44:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    sb t3, 0(t0)  # #] t3, 0(t0)
    li a4, 8
    bge a5, a4, _l45
_l45:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    sw a0, 0(t0)  # #] a0, 0(t0)
_l36:
    la t0, vals
    add t0, t0, t1
    sw a1, 0(t0)  # #] a1, 0(t0)
    addi a5, a5, 0
    li t0, 13
    beq a5, t0, _l46
_l46:
    li a0, 19
    li a1, 190
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l47:
    beqz t5, _l48
    li t4, 0
_l49:
    bge t4, a4, _l50
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l51
    addi a3, a6, 0
_l51:
    bne t1, t3, _l52
_l52:
    addi t4, t4, 1
    j _l49
_l50:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    addi a2, a6, 0
    li t5, 0
_l55:
_l54:
    j _l47
_l48:
    addi a5, a2, 0
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l57:
    beqz t5, _l58
    li t4, 0
_l59:
    bge t4, a4, _l60
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    blt t1, t2, _l61
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l61:
    addi t4, t4, 1
    j _l59
_l60:
    beqz t5, _l62
_l62:
    j _l57
_l58:
    addi a5, a2, 0
    bne a5, a6, _l64
_l64:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    sb t3, 0(t0)  # #] t3, 0(t0)
    li a4, 8
    bge a5, a4, _l65
_l65:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    sw a0, 0(t0)  # #] a0, 0(t0)
_l56:
    la t0, vals
    add t0, t0, t1
    sw a1, 0(t0)  # #] a1, 0(t0)
    addi a5, a5, 0
    li t0, 14
    beq a5, t0, _l66
_l66:
    li a0, 28
    li a1, 280
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l67:
    beqz t5, _l68
    li t4, 0
_l69:
    bge t4, a4, _l70
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l71
    addi a3, a6, 0
_l71:
    bne t1, t3, _l72
_l72:
    addi t4, t4, 1
    j _l69
_l70:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    addi a2, a6, 0
    li t5, 0
_l75:
_l74:
    j _l67
_l68:
    addi a5, a2, 0
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l77:
    beqz t5, _l78
    li t4, 0
_l79:
    bge t4, a4, _l80
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    blt t1, t2, _l81
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l81:
    addi t4, t4, 1
    j _l79
_l80:
    beqz t5, _l82
_l82:
    j _l77
_l78:
    addi a5, a2, 0
    bne a5, a6, _l84
_l84:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    sb t3, 0(t0)  # #] t3, 0(t0)
    li a4, 8
    bge a5, a4, _l85
_l85:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    sw a0, 0(t0)  # #] a0, 0(t0)
_l76:
    la t0, vals
    add t0, t0, t1
    sw a1, 0(t0)  # #] a1, 0(t0)
    addi a5, a5, 0
    li t0, 15
    beq a5, t0, _l86
_l86:
    li a0, 2049
    li a1, 20490
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l87:
    beqz t5, _l88
    li t4, 0
_l89:
    bge t4, a4, _l90
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l91
    addi a3, a6, 0
_l91:
    bne t1, t3, _l92
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    bne t0, a0, _l93
_l93:
_l92:
    addi t4, t4, 1
    j _l89
_l90:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    addi a2, a6, 0
    li t5, 0
_l95:
_l94:
    j _l87
_l88:
    addi a5, a2, 0
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l97:
    beqz t5, _l98
    li t4, 0
_l99:
    bge t4, a4, _l100
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    blt t1, t2, _l101
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l101:
    addi t4, t4, 1
    j _l99
_l100:
    beqz t5, _l102
_l102:
    j _l97
_l98:
    addi a5, a2, 0
    bne a5, a6, _l104
_l104:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    sb t3, 0(t0)  # #] t3, 0(t0)
    li a4, 8
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    sb t3, 0(t0)  # #] t3, 0(t0)
_l105:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    sw a0, 0(t0)  # #] a0, 0(t0)
_l96:
    la t0, vals
    add t0, t0, t1
    sw a1, 0(t0)  # #] a1, 0(t0)
    addi a5, a5, 0
    li t0, 0
    beq a5, t0, _l106
_l106:
    li a0, 86
    li a1, 860
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l107:
    beqz t5, _l108
    li t4, 0
_l109:
    bge t4, a4, _l110
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l111
    addi a3, a6, 0
_l111:
    bne t1, t3, _l112
_l112:
    addi t4, t4, 1
    j _l109
_l110:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    addi a2, a6, 0
    li t5, 0
_l115:
_l114:
    j _l107
_l108:
    addi a5, a2, 0
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l117:
    beqz t5, _l118
    li t4, 0
_l119:
    bge t4, a4, _l120
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    blt t1, t2, _l121
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l121:
    addi t4, t4, 1
    j _l119
_l120:
    beqz t5, _l122
_l122:
    j _l117
_l118:
    addi a5, a2, 0
    bne a5, a6, _l124
_l124:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    sb t3, 0(t0)  # #] t3, 0(t0)
    li a4, 8
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    sb t3, 0(t0)  # #] t3, 0(t0)
_l125:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    sw a0, 0(t0)  # #] a0, 0(t0)
_l116:
    la t0, vals
    add t0, t0, t1
    sw a1, 0(t0)  # #] a1, 0(t0)
    addi a5, a5, 0
    li t0, 1
    beq a5, t0, _l126
_l126:
    li a0, 95
    li a1, 950
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l127:
    beqz t5, _l128
    li t4, 0
_l129:
    bge t4, a4, _l130
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l131
    addi a3, a6, 0
_l131:
    bne t1, t3, _l132
_l132:
    addi t4, t4, 1
    j _l129
_l130:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    addi a2, a6, 0
    li t5, 0
_l135:
_l134:
    j _l127
_l128:
    addi a5, a2, 0
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l137:
    beqz t5, _l138
    li t4, 0
_l139:
    bge t4, a4, _l140
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    blt t1, t2, _l141
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l141:
    addi t4, t4, 1
    j _l139
_l140:
    beqz t5, _l142
_l142:
    j _l137
_l138:
    addi a5, a2, 0
    bne a5, a6, _l144
_l144:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    sb t3, 0(t0)  # #] t3, 0(t0)
    li a4, 8
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    sb t3, 0(t0)  # #] t3, 0(t0)
_l145:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    sw a0, 0(t0)  # #] a0, 0(t0)
_l136:
    la t0, vals
    add t0, t0, t1
    sw a1, 0(t0)  # #] a1, 0(t0)
    addi a5, a5, 0
    li t0, 2
    beq a5, t0, _l146
_l146:
    li a0, 104
    li a1, 1040
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l147:
    beqz t5, _l148
    li t4, 0
_l149:
    bge t4, a4, _l150
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l151
    addi a3, a6, 0
_l151:
    bne t1, t3, _l152
_l152:
    addi t4, t4, 1
    j _l149
_l150:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    addi a2, a6, 0
    li t5, 0
_l155:
_l154:
    j _l147
_l148:
    addi a5, a2, 0
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l157:
    beqz t5, _l158
    li t4, 0
_l159:
    bge t4, a4, _l160
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    blt t1, t2, _l161
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l161:
    addi t4, t4, 1
    j _l159
_l160:
    beqz t5, _l162
_l162:
    j _l157
_l158:
    addi a5, a2, 0
    bne a5, a6, _l164
_l164:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    sb t3, 0(t0)  # #] t3, 0(t0)
    li a4, 8
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    sb t3, 0(t0)  # #] t3, 0(t0)
_l165:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    sw a0, 0(t0)  # #] a0, 0(t0)
_l156:
    la t0, vals
    add t0, t0, t1
    sw a1, 0(t0)  # #] a1, 0(t0)
    addi a5, a5, 0
    li t0, 3
    beq a5, t0, _l166
_l166:
    li a0, 113
    li a1, 1130
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l167:
    beqz t5, _l168
    li t4, 0
_l169:
    bge t4, a4, _l170
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l171
    addi a3, a6, 0
_l171:
    bne t1, t3, _l172
_l172:
    addi t4, t4, 1
    j _l169
_l170:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l175
    addi a2, a6, 0
    li t5, 0
_l175:
_l174:
    j _l167
_l168:
    addi a5, a2, 0
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l177:
    beqz t5, _l178
    li t4, 0
_l179:
    bge t4, a4, _l180
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    blt t1, t2, _l181
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l181:
    addi t4, t4, 1
    j _l179
_l180:
    beqz t5, _l182
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l183
_l183:
_l182:
    j _l177
_l178:
    addi a5, a2, 0
    bne a5, a6, _l184
_l184:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    sb t3, 0(t0)  # #] t3, 0(t0)
    li a4, 8
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    sb t3, 0(t0)  # #] t3, 0(t0)
_l185:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    sw a0, 0(t0)  # #] a0, 0(t0)
_l176:
    la t0, vals
    add t0, t0, t1
    sw a1, 0(t0)  # #] a1, 0(t0)
    addi a5, a5, 0
    li t0, 4
    beq a5, t0, _l186
_l186:
    li a0, 30
    li a1, 300
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l187:
    beqz t5, _l188
    li t4, 0
_l189:
    bge t4, a4, _l190
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l191
    addi a3, a6, 0
_l191:
    bne t1, t3, _l192
_l192:
    addi t4, t4, 1
    j _l189
_l190:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    addi a2, a6, 0
    li t5, 0
_l195:
_l194:
    j _l187
_l188:
    addi a5, a2, 0
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l197:
    beqz t5, _l198
    li t4, 0
_l199:
    bge t4, a4, _l200
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    blt t1, t2, _l201
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l201:
    addi t4, t4, 1
    j _l199
_l200:
    beqz t5, _l202
_l202:
    j _l197
_l198:
    addi a5, a2, 0
    bne a5, a6, _l204
_l204:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    sb t3, 0(t0)  # #] t3, 0(t0)
    li a4, 8
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    sb t3, 0(t0)  # #] t3, 0(t0)
_l205:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    sw a0, 0(t0)  # #] a0, 0(t0)
_l196:
    la t0, vals
    add t0, t0, t1
    sw a1, 0(t0)  # #] a1, 0(t0)
    addi a5, a5, 0
    li t0, 5
    beq a5, t0, _l206
_l206:
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
_l207:
    beqz t5, _l208
    li t4, 0
_l209:
    bge t4, a4, _l210
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l211
    addi a3, a6, 0
_l211:
    bne t1, t3, _l212
_l212:
    addi t4, t4, 1
    j _l209
_l210:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    addi a2, a6, 0
    li t5, 0
_l215:
_l214:
    j _l207
_l208:
    addi a5, a2, 0
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l217:
    beqz t5, _l218
    li t4, 0
_l219:
    bge t4, a4, _l220
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l221:
    addi t4, t4, 1
    j _l219
_l220:
    beqz t5, _l222
_l222:
    j _l217
_l218:
    addi a5, a2, 0
    bne a5, a6, _l224
_l224:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    sb t3, 0(t0)  # #] t3, 0(t0)
    li a4, 8
    bge a5, a4, _l225
_l225:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    sw a0, 0(t0)  # #] a0, 0(t0)
_l216:
    la t0, vals
    add t0, t0, t1
    sw a1, 0(t0)  # #] a1, 0(t0)
    addi a5, a5, 0
    li t0, 8
    beq a5, t0, _l226
_l226:
    li a0, 11
    li a1, 111
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l227:
    beqz t5, _l228
    li t4, 0
_l229:
    bge t4, a4, _l230
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l231
    addi a3, a6, 0
_l231:
    bne t1, t3, _l232
_l232:
    addi t4, t4, 1
    j _l229
_l230:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    addi a2, a6, 0
    li t5, 0
_l235:
_l234:
    j _l227
_l228:
    addi a5, a2, 0
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l237:
    beqz t5, _l238
    li t4, 0
_l239:
    bge t4, a4, _l240
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    blt t1, t2, _l241
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l241:
    addi t4, t4, 1
    j _l239
_l240:
    beqz t5, _l242
_l242:
    j _l237
_l238:
    addi a5, a2, 0
    bne a5, a6, _l244
_l244:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    sb t3, 0(t0)  # #] t3, 0(t0)
    li a4, 8
    bge a5, a4, _l245
_l245:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    sw a0, 0(t0)  # #] a0, 0(t0)
_l236:
    la t0, vals
    add t0, t0, t1
    sw a1, 0(t0)  # #] a1, 0(t0)
    addi a5, a5, 0
    li t0, 9
    beq a5, t0, _l246
_l246:
    li a0, 1
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l247:
    beqz t5, _l248
    li t4, 0
_l249:
    bge t4, a4, _l250
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l251
_l251:
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l253:
_l252:
    addi t4, t4, 1
    j _l249
_l250:
    beqz t5, _l254
_l254:
    j _l247
_l248:
    addi a4, a2, 0
    li t0, 12
    beq a4, t0, _l256
_l256:
    la t0, vals
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    li t0, 100
    beq t2, t0, _l257
_l257:
    li a0, 2049
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l258:
    beqz t5, _l259
    li t4, 0
_l260:
    bge t4, a4, _l261
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l262
_l262:
    bne t1, t3, _l263
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    bne t0, a0, _l264
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l264:
_l263:
    addi t4, t4, 1
    j _l260
_l261:
    beqz t5, _l265
_l265:
    j _l258
_l259:
    addi a4, a2, 0
    li t0, 0
    beq a4, t0, _l267
_l267:
    la t0, vals
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    li t0, 20490
    beq t2, t0, _l268
_l268:
    li a0, 113
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l269:
    beqz t5, _l270
    li t4, 0
_l271:
    bge t4, a4, _l272
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l273
_l273:
    bne t1, t3, _l274
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l275:
_l274:
    addi t4, t4, 1
    j _l271
_l272:
    beqz t5, _l276
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l277
_l277:
_l276:
    j _l269
_l270:
    addi a4, a2, 0
    li t0, 4
    beq a4, t0, _l278
_l278:
    la t0, vals
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    li t0, 1130
    beq t2, t0, _l279
_l279:
    li a0, 30
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l280:
    beqz t5, _l281
    li t4, 0
_l282:
    bge t4, a4, _l283
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l284
_l284:
    bne t1, t3, _l285
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l286:
_l285:
    addi t4, t4, 1
    j _l282
_l283:
    beqz t5, _l287
_l287:
    j _l280
_l281:
    addi a4, a2, 0
    li t0, 5
    beq a4, t0, _l289
_l289:
    la t0, vals
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    li t0, 300
    beq t2, t0, _l290
_l290:
    li a0, 2
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l291:
    beqz t5, _l292
    li t4, 0
_l293:
    bge t4, a4, _l294
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l295
_l295:
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l297:
_l296:
    addi t4, t4, 1
    j _l293
_l294:
    beqz t5, _l298
_l298:
    j _l291
_l292:
    addi a4, a2, 0
    li t0, 8
    beq a4, t0, _l300
_l300:
    la t0, vals
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    li t0, 20
    beq t2, t0, _l301
_l301:
    li a0, 11
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l302:
    beqz t5, _l303
    li t4, 0
_l304:
    bge t4, a4, _l305
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l306
_l306:
    bne t1, t3, _l307
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l308:
_l307:
    addi t4, t4, 1
    j _l304
_l305:
    beqz t5, _l309
_l309:
    j _l302
_l303:
    addi a4, a2, 0
    li t0, 9
    beq a4, t0, _l311
_l311:
    la t0, vals
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    li t0, 111
    beq t2, t0, _l312
_l312:
    li a0, 122
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l313:
    beqz t5, _l314
    li t4, 0
_l315:
    bge t4, a4, _l316
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l317
    addi a3, a6, 0
_l317:
    bne t1, t3, _l318
_l318:
    addi t4, t4, 1
    j _l315
_l316:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l321
    addi a2, a6, 0
    li t5, 0
_l321:
_l320:
    j _l313
_l314:
    addi a4, a2, 0
    beq a4, a6, _l322
_l322:
    li a0, 4097
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l323:
    beqz t5, _l324
    li t4, 0
_l325:
    bge t4, a4, _l326
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l327
    addi a3, a6, 0
_l327:
    bne t1, t3, _l328
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    bne t0, a0, _l329
_l329:
_l328:
    addi t4, t4, 1
    j _l325
_l326:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l331
    addi a2, a6, 0
    li t5, 0
_l331:
_l330:
    j _l323
_l324:
    addi a4, a2, 0
    beq a4, a6, _l332
_l332:
    li a0, 39
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l333:
    beqz t5, _l334
    li t4, 0
_l335:
    bge t4, a4, _l336
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l337
    addi a3, a6, 0
_l337:
    bne t1, t3, _l338
_l338:
    addi t4, t4, 1
    j _l335
_l336:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    addi a2, a6, 0
    li t5, 0
_l341:
_l340:
    j _l333
_l334:
    addi a4, a2, 0
    beq a4, a6, _l342
_l342:
    li a0, 19
    li a1, 191
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l343:
    beqz t5, _l344
    li t4, 0
_l345:
    bge t4, a4, _l346
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l347
_l347:
    bne t1, t3, _l348
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l349:
_l348:
    addi t4, t4, 1
    j _l345
_l346:
    beqz t5, _l350
_l350:
    j _l343
_l344:
    addi a5, a2, 0
    bne a5, a6, _l352
_l352:
    la t0, vals
    add t0, t0, t1
    sw a1, 0(t0)  # #] a1, 0(t0)
    addi a5, a5, 0
    li t0, 14
    beq a5, t0, _l362
_l362:
    li a0, 19
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l363:
    beqz t5, _l364
    li t4, 0
_l365:
    bge t4, a4, _l366
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l367
_l367:
    bne t1, t3, _l368
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l369:
_l368:
    addi t4, t4, 1
    j _l365
_l366:
    beqz t5, _l370
_l370:
    j _l363
_l364:
    addi a4, a2, 0
    li t0, 14
    beq a4, t0, _l372
_l372:
    la t0, vals
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    li t0, 191
    beq t2, t0, _l373
_l373:
    li a0, 86
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l374:
    beqz t5, _l375
    li t4, 0
_l376:
    bge t4, a4, _l377
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l378
_l378:
    bne t1, t3, _l379
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l380:
_l379:
    addi t4, t4, 1
    j _l376
_l377:
    beqz t5, _l381
_l381:
    j _l374
_l375:
    addi a5, a2, 0
    add a2, a5, a6
    addi a2, a2, -8
    rem a2, a2, a6
    addi a2, a2, 7
    li t2, 128
    li a4, 8
    li a3, 0
    addi t1, a2, 0
    li t5, 1
_l384:
    beqz t5, _l385
    la t0, ctrl
    add t0, t0, t1
    lbu t0, 0(t0)  # #[ t0, 0(t0)
    bne t0, t2, _l386
    li t5, 0
_l386:
    beqz t5, _l387
    addi a3, a3, 1
    addi t1, t1, -1
    bne a3, a4, _l388
_l388:
_l387:
    j _l384
_l385:
    addi a2, a3, 0
    li t2, 128
    li a4, 8
    li a3, 0
    addi t1, a5, 0
    li t5, 1
_l389:
    beqz t5, _l390
    la t0, ctrl
    add t0, t0, t1
    lbu t0, 0(t0)  # #[ t0, 0(t0)
    bne t0, t2, _l391
    li t5, 0
_l391:
    beqz t5, _l392
    addi a3, a3, 1
    addi t1, t1, 1
    bne a3, a4, _l393
_l393:
_l392:
    j _l389
_l390:
    addi a3, a3, 0
    add a3, a3, a2
    li a4, 8
    li t3, 254
    bge a3, a4, _l394
_l394:
    la t0, ctrl
    add t0, t0, a5
    sb t3, 0(t0)  # #] t3, 0(t0)
    li a4, 8
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    sb t3, 0(t0)  # #] t3, 0(t0)
_l395:
_l383:
    addi a5, a5, 0
    li t0, 1
    beq a5, t0, _l396
_l396:
    la t0, ctrl
    lbu t1, 1(t0)  # #[ t1, 1(t0)
    li t2, 254
    beq t1, t2, _l397
_l397:
    la t0, ctrl
    lbu t1, 17(t0)  # #[ t1, 17(t0)
    li t2, 254
    beq t1, t2, _l398
_l398:
    li a0, 113
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l399:
    beqz t5, _l400
    li t4, 0
_l401:
    bge t4, a4, _l402
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l403
_l403:
    bne t1, t3, _l404
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l405:
_l404:
    addi t4, t4, 1
    j _l401
_l402:
    beqz t5, _l406
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l407
_l407:
_l406:
    j _l399
_l400:
    addi a4, a2, 0
    li t0, 4
    beq a4, t0, _l408
_l408:
    la t0, vals
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    li t0, 1130
    beq t2, t0, _l409
_l409:
    li a0, 86
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l410:
    beqz t5, _l411
    li t4, 0
_l412:
    bge t4, a4, _l413
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l414
    addi a3, a6, 0
_l414:
    bne t1, t3, _l415
_l415:
    addi t4, t4, 1
    j _l412
_l413:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l418
    addi a2, a6, 0
    li t5, 0
_l418:
_l417:
    j _l410
_l411:
    addi a4, a2, 0
    beq a4, a6, _l419
_l419:
    li a0, 95
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l420:
    beqz t5, _l421
    li t4, 0
_l422:
    bge t4, a4, _l423
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l424
_l424:
    bne t1, t3, _l425
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l426:
_l425:
    addi t4, t4, 1
    j _l422
_l423:
    beqz t5, _l427
_l427:
    j _l420
_l421:
    addi a4, a2, 0
    li t0, 2
    beq a4, t0, _l429
_l429:
    la t0, vals
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    li t0, 950
    beq t2, t0, _l430
_l430:
    li a0, 86
    li a1, 861
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l431:
    beqz t5, _l432
    li t4, 0
_l433:
    bge t4, a4, _l434
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l435
    addi a3, a6, 0
_l435:
    bne t1, t3, _l436
_l436:
    addi t4, t4, 1
    j _l433
_l434:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l439
    addi a2, a6, 0
    li t5, 0
_l439:
_l438:
    j _l431
_l432:
    addi a5, a2, 0
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    li a4, 8
    li a3, 0
    li t5, 1
_l441:
    beqz t5, _l442
    li t4, 0
_l443:
    bge t4, a4, _l444
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    blt t1, t2, _l445
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l445:
    addi t4, t4, 1
    j _l443
_l444:
    beqz t5, _l446
_l446:
    j _l441
_l442:
    addi a5, a2, 0
    bne a5, a6, _l448
_l448:
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    rem t3, t3, t2
    la t0, ctrl
    add t0, t0, a5
    sb t3, 0(t0)  # #] t3, 0(t0)
    li a4, 8
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    sb t3, 0(t0)  # #] t3, 0(t0)
_l449:
    add t1, a5, a5
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    sw a0, 0(t0)  # #] a0, 0(t0)
_l440:
    la t0, vals
    add t0, t0, t1
    sw a1, 0(t0)  # #] a1, 0(t0)
    addi a5, a5, 0
    li t0, 1
    beq a5, t0, _l450
_l450:
    li a0, 86
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l451:
    beqz t5, _l452
    li t4, 0
_l453:
    bge t4, a4, _l454
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l455
_l455:
    bne t1, t3, _l456
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l457:
_l456:
    addi t4, t4, 1
    j _l453
_l454:
    beqz t5, _l458
_l458:
    j _l451
_l452:
    addi a4, a2, 0
    li t0, 1
    beq a4, t0, _l460
_l460:
    la t0, vals
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    li t0, 861
    beq t2, t0, _l461
_l461:
    la t0, ctrl
    lbu t1, 1(t0)  # #[ t1, 1(t0)
    li t2, 122
    beq t1, t2, _l462
_l462:
    la t0, ctrl
    lbu t1, 17(t0)  # #[ t1, 17(t0)
    li t2, 122
    beq t1, t2, _l463
_l463:
    li a0, 2
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l464:
    beqz t5, _l465
    li t4, 0
_l466:
    bge t4, a4, _l467
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l468
_l468:
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l470:
_l469:
    addi t4, t4, 1
    j _l466
_l467:
    beqz t5, _l471
_l471:
    j _l464
_l465:
    addi a5, a2, 0
    add a2, a5, a6
    addi a2, a2, -8
    rem a2, a2, a6
    addi a2, a2, 7
    li t2, 128
    li a4, 8
    li a3, 0
    addi t1, a2, 0
    li t5, 1
_l474:
    beqz t5, _l475
    la t0, ctrl
    add t0, t0, t1
    lbu t0, 0(t0)  # #[ t0, 0(t0)
    li t5, 0
_l476:
    beqz t5, _l477
_l477:
    j _l474
_l475:
    addi a2, a3, 0
    li t2, 128
    li a4, 8
    li a3, 0
    addi t1, a5, 0
    li t5, 1
_l479:
    beqz t5, _l480
    la t0, ctrl
    add t0, t0, t1
    lbu t0, 0(t0)  # #[ t0, 0(t0)
    bne t0, t2, _l481
    li t5, 0
_l481:
    beqz t5, _l482
    addi a3, a3, 1
    addi t1, t1, 1
    bne a3, a4, _l483
_l483:
_l482:
    j _l479
_l480:
    addi a3, a3, 0
    add a3, a3, a2
    li a4, 8
    li t3, 254
    li t3, 128
_l484:
    la t0, ctrl
    add t0, t0, a5
    sb t3, 0(t0)  # #] t3, 0(t0)
    li a4, 8
    bge a5, a4, _l485
_l485:
_l473:
    addi a5, a5, 0
    li t0, 8
    beq a5, t0, _l486
_l486:
    la t0, ctrl
    lbu t1, 8(t0)  # #[ t1, 8(t0)
    li t2, 128
    beq t1, t2, _l487
_l487:
    li a0, 11
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l488:
    beqz t5, _l489
    li t4, 0
_l490:
    bge t4, a4, _l491
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l492
    addi a3, a6, 0
_l492:
    bne t1, t3, _l493
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l494:
_l493:
    addi t4, t4, 1
    j _l490
_l491:
    beqz t5, _l495
_l495:
    j _l488
_l489:
    addi a4, a2, 0
    li t0, 9
    beq a4, t0, _l497
_l497:
    la t0, vals
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    li t0, 111
    beq t2, t0, _l498
_l498:
    li a0, 2
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l499:
    beqz t5, _l500
    li t4, 0
_l501:
    bge t4, a4, _l502
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l503
    addi a3, a6, 0
_l503:
    bne t1, t3, _l504
_l504:
    addi t4, t4, 1
    j _l501
_l502:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    addi a2, a6, 0
    li t5, 0
_l507:
_l506:
    j _l499
_l500:
    addi a4, a2, 0
    beq a4, a6, _l508
_l508:
    li a0, 30
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l509:
    beqz t5, _l510
    li t4, 0
_l511:
    bge t4, a4, _l512
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l513
_l513:
    bne t1, t3, _l514
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l515:
_l514:
    addi t4, t4, 1
    j _l511
_l512:
    beqz t5, _l516
_l516:
    j _l509
_l510:
    addi a5, a2, 0
    add a2, a5, a6
    addi a2, a2, -8
    rem a2, a2, a6
    addi a2, a2, 7
    li t2, 128
    li a4, 8
    li a3, 0
    addi t1, a2, 0
    li t5, 1
_l519:
    beqz t5, _l520
    la t0, ctrl
    add t0, t0, t1
    lbu t0, 0(t0)  # #[ t0, 0(t0)
    bne t0, t2, _l521
_l521:
    addi a3, a3, 1
    addi t1, t1, -1
    bne a3, a4, _l523
    li t5, 0
_l523:
_l522:
    j _l519
_l520:
    addi a2, a3, 0
    li t2, 128
    li a4, 8
    li a3, 0
    addi t1, a5, 0
    li t5, 1
_l524:
    beqz t5, _l525
    la t0, ctrl
    add t0, t0, t1
    lbu t0, 0(t0)  # #[ t0, 0(t0)
    bne t0, t2, _l526
    li t5, 0
_l526:
    beqz t5, _l527
    addi a3, a3, 1
    addi t1, t1, 1
    bne a3, a4, _l528
_l528:
_l527:
    j _l524
_l525:
    addi a3, a3, 0
    add a3, a3, a2
    li a4, 8
    li t3, 254
    bge a3, a4, _l529
_l529:
    la t0, ctrl
    add t0, t0, a5
    sb t3, 0(t0)  # #] t3, 0(t0)
    li a4, 8
    add t1, a6, a5
    la t0, ctrl
    add t0, t0, t1
    sb t3, 0(t0)  # #] t3, 0(t0)
_l530:
_l518:
    addi a5, a5, 0
    li t0, 5
    beq a5, t0, _l531
_l531:
    la t0, ctrl
    lbu t1, 5(t0)  # #[ t1, 5(t0)
    li t2, 254
    beq t1, t2, _l532
_l532:
    la t0, ctrl
    lbu t1, 21(t0)  # #[ t1, 21(t0)
    li t2, 254
    beq t1, t2, _l533
_l533:
    li a0, 113
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l534:
    beqz t5, _l535
    li t4, 0
_l536:
    bge t4, a4, _l537
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l538
_l538:
    bne t1, t3, _l539
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l540:
_l539:
    addi t4, t4, 1
    j _l536
_l537:
    beqz t5, _l541
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    blt a3, a6, _l542
_l542:
_l541:
    j _l534
_l535:
    addi a4, a2, 0
    li t0, 4
    beq a4, t0, _l543
_l543:
    la t0, vals
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    li t0, 1130
    beq t2, t0, _l544
_l544:
    li a0, 30
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l545:
    beqz t5, _l546
    li t4, 0
_l547:
    bge t4, a4, _l548
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l549
    addi a3, a6, 0
_l549:
    bne t1, t3, _l550
_l550:
    addi t4, t4, 1
    j _l547
_l548:
    add a3, a3, a4
    add a2, a2, a3
    rem a2, a2, a6
    addi a2, a6, 0
    li t5, 0
_l553:
_l552:
    j _l545
_l546:
    addi a4, a2, 0
    beq a4, a6, _l554
_l554:
    li a0, 86
    li a4, 40503
    mul t3, a0, a4
    li t2, 128
    div a2, t3, t2
    rem a2, a2, a6
    rem t3, t3, t2
    li a4, 8
    li a3, 0
    li t5, 1
_l555:
    beqz t5, _l556
    li t4, 0
_l557:
    bge t4, a4, _l558
    add t1, a2, t4
    la t0, ctrl
    add t0, t0, t1
    lbu t1, 0(t0)  # #[ t1, 0(t0)
    bne t1, t2, _l559
_l559:
    bne t1, t3, _l560
    add t1, a2, t4
    rem t1, t1, a6
    add t1, t1, t1
    add t1, t1, t1
    la t0, keys
    add t0, t0, t1
    lwu t0, 0(t0)  # #[ t0, 0(t0)
    add a2, a2, t4
    rem a2, a2, a6
    li t5, 0
    addi t4, a4, 0
_l561:
_l560:
    addi t4, t4, 1
    j _l557
_l558:
    beqz t5, _l562
_l562:
    j _l555
_l556:
    addi a4, a2, 0
    li t0, 1
    beq a4, t0, _l564
_l564:
    la t0, vals
    add t0, t0, t1
    lwu t2, 0(t0)  # #[ t2, 0(t0)
    li t0, 861
    beq t2, t0, _l565
_l565:
    li t2, 128
    la t0, ctrl
    addi t1, a6, 0
    li a2, 0
_l566:
    beqz t1, _l567
    lbu t3, 0(t0)  # #[ t3, 0(t0)
    bge t3, t2, _l568
    addi a2, a2, 1
_l568:
    addi t0, t0, 1
    addi t1, t1, -1
    j _l566
_l567:
    addi a3, a2, 0
    li t0, 10
    beq a3, t0, _l569
_l569:
    addi t5, a3, 0
    #$ __local0 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local0
    addi t0, t0, 2
    li t1, 10
    li a2, 0
    bnez t5, _l570
_l570:
_l571:
    beqz t5, _l572
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)  # #] t2, 0(t0)
    addi a2, a2, 1
    j _l571
_l572:
    addi a1, t0, 0
    li a0, 1
    li a7, 64
    ecall
    #$ __str0 thread [u8 u8]
    la t0, __str0
    li t1, 32
    sb t1, 0(t0)
    li t1, 0
    sb t1, 1(t0)
    la a1, __str0
    li a2, 0
    lbu t0, 0(a1)  # #[ t0, 0(a1)
_l573:
    beqz t0, _l574
    addi a2, a2, 1
    addi a1, a1, 1
    lbu t0, 0(a1)  # #[ t0, 0(a1)
    j _l573
_l574:
    li a0, 1
    la a1, __str0
    li a7, 64
    ecall
    addi t5, a5, 0
    #$ __local1 thread [u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8]
    la t0, __local1
    addi t0, t0, 1
    li t1, 10
    li a2, 0
    bnez t5, _l575
_l575:
_l576:
    beqz t5, _l577
    rem t2, t5, t1
    div t5, t5, t1
    addi t2, t2, 48
    addi t0, t0, -1
    sb t2, 0(t0)  # #] t2, 0(t0)
    addi a2, a2, 1
    j _l576
_l577:
    addi a1, t0, 0
    li a0, 1
    li a7, 64
    ecall
    #$ __str1 thread [u8 u8]
    la t0, __str1
    li t1, 10
    sb t1, 0(t0)
    li t1, 0
    sb t1, 1(t0)
    la a1, __str1
    li a2, 0
    lbu t0, 0(a1)  # #[ t0, 0(a1)
_l578:
    beqz t0, _l579
    addi a2, a2, 1
    addi a1, a1, 1
    lbu t0, 0(a1)  # #[ t0, 0(a1)
    j _l578
_l579:
    li a0, 1
    la a1, __str1
    li a7, 64
    ecall
    li a0, 0
    li a7, 93
    ecall
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
__local0:
    .zero 2
    .balign 8
__local1:
    .zero 1
    .balign 8
__str0:
    .zero 2
    .balign 8
__str1:
    .zero 2
    .balign 8
ctrl:
    .zero 24
    .balign 8
keys:
    .zero 48
    .balign 8
vals:
    .zero 48
