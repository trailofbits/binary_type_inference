#include <time.h>
#include <stdio.h>
#include <stdint.h>

static uint32_t key_hash(const uint8_t *key, size_t key_size)
{
    uint64_t h = 0;
    for (int i = 0; i < key_size; i++) {
        h = h * 0x13377331 + key[i];
    }
    return h;
}

uint64_t H[0x100000];

int main()
{
    srand(time(NULL));
    uint32_t shift = rand();
    char tmp[8] = {0};
#define L 0x40
#define R 0x7f
    for (char a = L; a < R; a++) {
        tmp[0] = a;
        for (char b = L; b < R; b++) {
            tmp[1] = b;
            for (char c = L; c < R; c++) {
                tmp[2] = c;
                for (char d = L; d < R; d++) {
                    tmp[3] = d;
                    for (char e = L; e < R; e++) {
                        tmp[4] = e;
                        uint32_t h = key_hash(&tmp, 5) - shift;
                        if (h < 0x100000) {
                            if (H[h] == 0) {
                                H[h] = *(uint64_t *)&tmp;
                            } else {
                                printf("%s %s => %#08x\n", tmp, &H[h], h);
                            }
                        }
                    }
                }
            }
        }
    }
}
