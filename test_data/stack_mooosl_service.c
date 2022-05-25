#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>

static int recvuntil(void *buf, size_t n)
{
    for (int i = 0; i < n; i++) {
        char c;
        if (read(0, &c, 1) != 1) {
            return i;
        }
        ((char *)buf)[i] = c;
        if (c == '\n') {
            ((char *)buf)[i] = 0;
            return i;
        }
    }
    return n;
}

static int readint()
{
    char buf[0x10] = {0};
    recvuntil(&buf, sizeof(buf));
    return atoi(buf);
}

static size_t read_key(uint8_t **key)
{
    printf("key size: ");
    size_t key_size = readint();
    *key = calloc(1, key_size);
    printf("key content: ");
    return recvuntil(*key, key_size);
}

static size_t read_value(uint8_t **value)
{
    printf("value size: ");
    size_t value_size = readint();
    *value = calloc(1, value_size);
    printf("value content: ");
    return recvuntil(*value, value_size);
}

struct node {
    uint8_t *key;
    uint8_t *value;
    size_t key_size;
    size_t value_size;
    uint64_t hash;
    struct node *next;
    // struct node *prev;
};

static uint32_t key_hash(const uint8_t *key, size_t key_size)
{
    uint64_t h = 2021;
    for (int i = 0; i < key_size; i++) {
        h = h * 0x13377331 + key[i];
    }
    return h;
}

static void value_dump(const uint8_t *data, size_t size)
{
    printf("%#lx:", size);
    for (int i = 0; i < size; i++) {
        printf("%02x", data[i]);
    }
    puts("");
}

#define HASH_SIZE 0x1000
#define HASH_MASK (HASH_SIZE - 1)


static void menu()
{
    puts("1: store");
    puts("2: query");
    puts("3: delete");
    puts("4: exit");
    printf("option: ");
}

static struct node *lookup(struct node **list_heads, const uint8_t *key, size_t key_size)
{
    uint64_t h = key_hash(key, key_size);
    for (struct node *n = list_heads[h & HASH_MASK]; n; n = n->next) {
        if (n->hash == h && n->key_size == key_size && !memcmp(key, n->key, key_size)) {
            return n;
        }
    }
    return NULL;
}

static void store(struct node **list_heads)
{
    struct node *node = calloc(1, sizeof(struct node));
    node->key_size = read_key(&node->key);
    // always insert to the head, don't check duplicated entries
    node->value_size = read_value(&node->value);
    node->hash = key_hash(node->key, node->key_size);
    const uint32_t h = node->hash & HASH_MASK;
    struct node *next = list_heads[h];
    list_heads[h] = node;
    node->next = next;
    // node->prev = NULL;
    puts("ok");
}

static void query(struct node **list_heads)
{
    uint8_t *key = NULL;
    size_t key_size = read_key(&key);
    struct node *n = lookup(list_heads, key, key_size);
    if (n == NULL) {
        puts("err");
    } else {
        value_dump(n->value, n->value_size);
        puts("ok");
    }
    free(key);
}

static void delete(struct node **list_heads)
{
    uint8_t *key = NULL;
    size_t key_size = read_key(&key);
    struct node *n = lookup(list_heads, key, key_size);
    if (n == NULL) {
        puts("err");
    } else {
        /*
        if (n->prev == NULL) {
            list_heads[n->hash & HASH_MASK] = n->next;
        } else if (n->next != NULL) {
            n->prev->next = n->next;
            n->next->prev = NULL;
        } else {
            // bug: uaf
            // n->prev->next = NULL;
        }
        */
        struct node **p = &list_heads[n->hash & HASH_MASK];
        if (*p == n || n->next != NULL) {
            // above condition is buggy
            // remove `n` from the linked list
            while (*p != n) {
                p = &(*p)->next;
            }
            *p = n->next;
        } else {
            // uaf: if `n` is at the tail of the linked list
        }
        free(n->key);
        free(n->value);
        free(n);
        puts("ok");
    }
    free(key);
}

int main(int argc, char** argv) {
    struct node *list_heads[HASH_SIZE];
    setvbuf(stdout, NULL, _IONBF, 0);
    setvbuf(stderr, NULL, _IONBF, 0);
    while (1) {
        menu();
        int op = readint();
        switch (op) {
            case 1:
                store(list_heads);
                break;
            case 2:
                query(list_heads);
                break;
            case 3:
                delete(list_heads);
                break;
            case 4:
                puts("bye");
                exit(0);
            default:
                puts("invalid");
                exit(0);
        }
    }
    return 0;
}
