#include <stdbool.h>
#include "debug_uart.h"

#define INF -1
#define NINF -2

typedef enum {
    BIT,
    BYTE
} dataunit;

typedef enum {
    LSB,
    MSB
} endianness;

typedef struct {
    int start_byte;
    int start_bit;
    int end_byte;
    int end_bit;
} parsed_result;

int cur_byte_pos = 0;
int cur_bit_pos = 0;

unsigned char* TAPE;
int TAPE_LEN;

/*@ requires TAPE_LEN >= 0;
 *  requires \valid(TAPE+(0..(TAPE_LEN-1)));
 *  requires \valid(p.fsm_table+(0..(p.table_length-1)));
 *  requires cur_byte_pos < TAPE_LEN;
 *  assigns cur_byte_pos, cur_bit_pos;
 */
bool get_next_bit() {
    bool cur_symbol;
    if (cur_byte_pos >= TAPE_LEN) {
        debug_printf("cur_bit_pos: byte >= TAPE_LEN: %d\n", cur_byte_pos);
        return 0;
    }
    char cur_char = TAPE[cur_byte_pos];
    cur_symbol = 1 & (cur_char >> cur_bit_pos);
    cur_bit_pos++;
    if (cur_bit_pos >= 8) {
        cur_bit_pos = cur_bit_pos % 8;
        cur_byte_pos++;
    }
    return cur_symbol;
}

bool is_tape_available() {
    if ((cur_byte_pos + 1) < TAPE_LEN) {
        // some bytes remaining
        return 1;
    } else {
        if ((cur_byte_pos + 1) == TAPE_LEN) {
            // some bits left
            if (cur_bit_pos < 7) {
                return 1;
            }
        }
    }
    return 0;
}

void set_pos_end(parsed_result* r)
{
    r->end_bit  = cur_bit_pos;
    r->end_byte = cur_byte_pos;
    return;
}

void set_pos_start(parsed_result* r)
{
    r->start_bit  = cur_bit_pos;
    r->start_byte = cur_byte_pos;
    return;
}

/*@ requires TAPE_LEN >= 0
*/
unsigned char get_next_byte() {
    if (cur_byte_pos >= TAPE_LEN) {
        debug_printf("cur_byte_pos: >= TAPE_LEN: %d \n", cur_byte_pos);
        return 0;
    }

    bool cur_symbol;
    char cur_char = TAPE[cur_byte_pos];
    // printf("Read %d from tape at loc %d\n", cur_char, cur_byte_pos);
    cur_byte_pos++;
    return cur_char;
}

// set the value of the register to T
int tag_cons(dataunit unit, int size) {
    unsigned int tag_val = 0;

    if (unit == BIT) {
        for (int i = 0; i < size; ++i) {
            tag_val = tag_val | get_next_bit();
            tag_val = tag_val << 1;
        }
    } else {
        if (!(size <= 4)) { debug_write("size error in tag_cons\n");}
        for (int i = 0; i < size; ++i) {
            tag_val = get_next_byte();
            tag_val = tag_val << 8;
        }
    }
    debug_printf("| tagval: %d \n", tag_val);
    return tag_val;
};

// set the value of the counter register to L.
int len_cons(dataunit unit, endianness e, int size) {
    int len_val = 0;
    if (unit == BIT) {
        int i = 0;
        for (i = 0; i < size; ++i) {
            len_val = len_val | get_next_bit();
            len_val = len_val << 1;
        }
    } else {
        int i = 0;
        if (!(size <= 4)) { debug_write("size error in tag_cons\n");}
        for (i = 0; i < size; ++i) {
            len_val = get_next_byte();
            len_val = len_val << 8;
        }
    }
    // TODO: verify by lookahead

    // return read value
    return len_val;
};

// make lookup table and call that function.
// case function: generate this with code

// repeats construct r, n times
parsed_result repeat_cons(dataunit u, int n, int min, int max) {
    debug_write("repeat_cons: start\n");
    parsed_result r;
    set_pos_start(&r);
    if (n == INF) {
        // at least min items and at most max items
        if (u == BIT) {
            int i = 0;
            for (i = 0; i < min; ++i) {
                get_next_bit();
            }
            while (i <= max) {
                if (is_tape_available()) {
                    break;
                }
                get_next_bit();
                i++;
            }

            set_pos_end(&r);
            return r;
        } else {
            int i = 0;
            for (i = 0; i < min; ++i) {
                get_next_byte();
            }

            while (i <= max) {
                if (is_tape_available()) {
                    break;
                }
                get_next_byte();
                i++;
            }

            set_pos_end(&r);
            return r;
        }
    } else {
        if (u == BIT) {
            if (!(n <= 8)) {
                debug_write("error in  repeat_cons");
            }
            for (int i = 0; i < n; ++i) {
                get_next_bit();
            }
            set_pos_end(&r);
            return r;
        } else {
            for (int i = 0; i < n; ++i) {
                get_next_byte();
            }
            set_pos_end(&r);
            return r;
        }
    }
};


// We define a gloabl list of registers which store results.
unsigned int run_parser(unsigned char* input_buffer, int buffer_len) {
    cur_bit_pos = 0;
    cur_byte_pos = 0;
    TAPE = input_buffer;
    TAPE_LEN = buffer_len;

    // PDU
    int reg4144 = tag_cons(BIT, 4);
    // // RFU
    int reg4145 = tag_cons(BIT, 1);
    // ChSel
    int reg4146 = tag_cons(BIT, 1);
    // TxAdd
    int reg4147 = tag_cons(BIT, 1);
    // RxAdd
    int reg4148 = tag_cons(BIT, 1);
    int reg4149 = len_cons(BYTE, LSB, 2);

    debug_printf("| len cons: %d, tag: %04x \n", reg4149, reg4144);

    switch (reg4144) {
        case 0b0001: {
                        debug_write("tag 0b0001 and adv_direct_ind\n");
                         // :ADV_DIRECT_IND
                         // AdvA
                         parsed_result reg4150 = repeat_cons(BYTE, 6, NINF, INF);
                         // Target A
                         parsed_result reg4151 = repeat_cons(BYTE, 6, NINF, INF);
                         break;
                     }
        case 0b0011: {
                        debug_write("tag 0b0011 and scan_req\n");
                         // :SCAN_REQ
                         // ScanA
                         parsed_result  reg4152 = repeat_cons(BYTE, 6, NINF, INF);
                         // AdvA
                         parsed_result  reg4153 = repeat_cons(BYTE, 6, NINF, INF);
                         break;
                     }
        case 0b0000: {
                     debug_write("tag 0000 and ADV_IDV\n");
                     // :ADV_IDV
                     // AdvA
                     parsed_result  reg4154 = repeat_cons(BYTE, 6, NINF, INF);
                     // repeat 0 31 bytes
                     parsed_result  reg4155 = repeat_cons(BYTE, INF, 0, 31);
                     break;
                 }
        case 0b0101: {
                     debug_write("tag CONNECT_IND\n");
                         // :CONNECT_IND
                         // InitA
                         parsed_result  reg4156 = repeat_cons(BYTE, 6, NINF, INF);
                         // AdvA
                         parsed_result  reg4157 = repeat_cons(BYTE, 6, NINF, INF);
                         // AA
                         parsed_result  reg4158 = repeat_cons(BYTE, 4, NINF, INF);
                         // CRCInit
                         parsed_result  reg4159 = repeat_cons(BYTE, 3, NINF, INF);
                         // WinSize
                         parsed_result  reg4160 = repeat_cons(BYTE, 1, NINF, INF);
                         // WinOffset
                         parsed_result  reg4161 = repeat_cons(BYTE, 2, NINF, INF);
                         // Interval
                         parsed_result  reg4162 = repeat_cons(BYTE, 2, NINF, INF);
                         // Latency
                         parsed_result  reg4163 = repeat_cons(BYTE, 2, NINF, INF);
                         // Timeout
                         parsed_result  reg4164 = repeat_cons(BYTE, 2, NINF, INF);
                         // ChM
                         parsed_result  reg4165 = repeat_cons(BYTE, 5, NINF, INF);
                         // Hop
                         parsed_result  reg4166 = repeat_cons(BYTE, 5, NINF, INF);
                         // SCA
                         parsed_result  reg4167 = repeat_cons(BYTE, 3, NINF, INF);
                         break;
                     }
        case 0b0010: {
            debug_write("tag ADV_CONNECT_IND\n");
                         // :ADV_NONCONN_IND
                         // AdvA
                         parsed_result  reg4168 = repeat_cons(BYTE, 6, NINF, INF);
                         // repeat 0 31 bytes
                         parsed_result  reg4169 = repeat_cons(BYTE, INF, 0, 31);
                         break;
                     }
        case 0b0111: {
            debug_write("tag ADV_EXT_IND\n");
                         // :ADV_EXT_IND
                         int reg4170 = len_cons(BIT, LSB, 6);
                         // AdvMode
                         parsed_result  reg4171 = repeat_cons(BYTE, 2, NINF, INF);
                         if (reg4170 == 0) {} else {
                             // repeat 0 63 bytes
                             parsed_result  reg4172 = repeat_cons(BYTE, reg4170, 0, 63);
                         }
                         // repeat 0 - 254 bytes
                         parsed_result  reg4173 = repeat_cons(BYTE, INF, 0, 254);
                         break;
                     }
        case 0b1000: {
            debug_write("tag AUX_CONNECT_RSP\n");
                         // :AUX_CONNECT_RSP
                         int reg4174 = len_cons(BIT, LSB, 6);
                         // AdvMode
                         parsed_result  reg4175 = repeat_cons(BYTE, 2, NINF, INF);
                         if (reg4174 == 0) {} else {
                             // repeat 0 63 bytes
                             parsed_result  reg4176 = repeat_cons(BYTE, reg4174, 0, 63);
                         }
                         // repeat 0 - 254 bytes
                         parsed_result  reg4177 = repeat_cons(BYTE, INF, 0, 254);
                         break;
                     }
        case 0b0100: {
            debug_write("tag SCAN_RSP\n");
                         // :SCAN_RSP
                         // AdvA
                         parsed_result  reg4178 = repeat_cons(BYTE, 6, NINF, INF);
                         // repeat 0 31 bytes
                         parsed_result  reg4179 = repeat_cons(BYTE, INF, 0, 31);
                         break;
                     }
        case 0b0110: {
            debug_write("tag ADV_SCAN_IND\n");
                         // :ADV_SCAN_IND
                         // AdvA
                         parsed_result  reg4180 = repeat_cons(BYTE, 6, NINF, INF);
                         // repeat 0 31 bytes
                         parsed_result  reg4181 = repeat_cons(BYTE, INF, 0, 31);
                         break;
                     }
        default:
                debug_write("ERROR: None matched case expression!");
    }
    debug_write("parse finished.\n");
    return 0;
};
