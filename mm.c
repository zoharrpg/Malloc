/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * TODO: insert your documentation here. :)
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Your Name <andrewid@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printf(...) ((void)printf(__VA_ARGS__))
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, these should emit no code whatsoever,
 * not even from evaluation of argument expressions.  However,
 * argument expressions should still be syntax-checked and should
 * count as uses of any variables involved.  This used to use a
 * straightforward hack involving sizeof(), but that can sometimes
 * provoke warnings about misuse of sizeof().  I _hope_ that this
 * newer, less straightforward hack will be more robust.
 * Hat tip to Stack Overflow poster chqrlie (see
 * https://stackoverflow.com/questions/72647780).
 */
#define dbg_discard_expr_(...) ((void)((0) && printf(__VA_ARGS__)))
#define dbg_requires(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_assert(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_ensures(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_printf(...) dbg_discard_expr_(__VA_ARGS__)
#define dbg_printheap(...) ((void)((0) && print_heap(__VA_ARGS__)))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = 2 * dsize;

/**
 *The minimum size of memory that can request for heap
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * TODO: Mask for extract the LSB
 */
static const word_t alloc_mask = 0x1;

/**
 * TODO: explain what size_mask is
 * mask for extracting bit excluding 4 bits from LSB
 */
static const word_t size_mask = ~(word_t)0xF;

/**
 * store pointer of next and prev block
 */
struct Pointer {
    struct block *next;
    struct block *prev;
};

/**
 * union data type
 */
union Data {
    struct Pointer pointer;
    char payload[0];
};

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;

    /**
     * @brief A pointer to the block payload.
     *
     * TODO: feel free to delete this comment once you've read it carefully.
     * We don't know what the size of the payload will be, so we will declare
     * it as a zero-length array, which is a GNU compiler extension. This will
     * allow us to obtain a pointer to the start of the payload. (The similar
     * standard-C feature of "flexible array members" won't work here because
     * those are not allowed to be members of a union.)
     *
     * WARNING: A zero-length array must be the last element in a struct, so
     * there should not be any struct fields after it. For this lab, we will
     * allow you to include a zero-length array in a union, as long as the
     * union is the last field in its containing struct. However, this is
     * compiler-specific behavior and should be avoided in general.
     *
     * WARNING: DO NOT cast this pointer to/from other types! Instead, you
     * should use a union to alias this zero-length array with another struct,
     * in order to store additional types of data in the payload memory.
     */
    union Data data;

    /*
     * TODO: delete or replace this comment once you've thought about it.
     * Why can't we declare the block footer here as part of the struct?
     * Why do we even have footers -- will the code work fine without them?
     * which functions actually use the data contained in footers?
     */
} block_t;
#define LIST_NUM 15
#define MAX_SIZE 262144

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

block_t *seglist[LIST_NUM];

static const word_t prev_alloc_mask = 0x2;

/** the head of the free list*/

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, data.payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->data.payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->data.payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - wsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == (char *)mem_heap_hi() - 7);
    block->header = pack(0, true);
}

/**
 * Get next pointer
 */
static block_t **get_next(block_t *block) {
    return &(block->data.pointer.next);
}
/**
 * get previous pointer
 */
static block_t **get_prev(block_t *block) {

    return &(block->data.pointer.prev);
}

/**
 * Add free list
 */
static void add_free_list(block_t *block, block_t **free_head) {
    block_t **next = get_next(block);
    block_t **prev = get_prev(block);
    if (block == *free_head) {
        return;
    }
    if (*free_head == NULL) {
        *free_head = block;

        *next = NULL;
        *prev = NULL;
    } else {
        block_t **head_pre = get_prev(*free_head);

        *head_pre = block;
        *next = *free_head;
        *prev = NULL;
        *free_head = block;
    }
}

/**
 * remove from list
 */
static void remove_from_list(block_t *block, block_t **free_head) {

    if (block == *free_head) {
        block_t **next = get_next(block);
        if (*next != NULL) {
            block_t **next_pre = get_prev(*next);
            *next_pre = NULL;
            *free_head = *next;
            *next = NULL;

        } else {
            *free_head = NULL;
        }

    } else {
        block_t **next = get_next(block);
        block_t **prev = get_prev(block);
        if (*next != NULL) {
            block_t **prev_next = get_next(*prev);
            block_t **next_prev = get_prev(*next);
            *prev_next = *next;
            *next_prev = *prev;

        } else {
            block_t **prev_next = get_next(*prev);

            *prev_next = *next;
        }

        *prev = NULL;
        *next = NULL;
    }
}
/**
 * search seglist
 */
static block_t **search_seg(block_t *block) {
    size_t size = get_size(block);
    if (size > MAX_SIZE) {
        return &seglist[LIST_NUM - 1];
    }

    for (size_t i = 0; i < LIST_NUM; i++) {

        size_t current_size = 1 << (i + 5);
        if (current_size >= size) {

            return &seglist[i];
        }
    }
    printf("This is a big error\n");
    return NULL;
}
static size_t search_seg_by_size(size_t size) {
    if (size > MAX_SIZE) {
        return LIST_NUM - 1;
    }

    for (size_t i = 0; i < LIST_NUM; i++) {

        size_t current_size = 1 << (i + 5);
        if (current_size >= size) {

            return i;
        }
    }
    printf("This is a big error\n");
    return 1;
}

static void add_seg_list(block_t *block) {
    block_t **head = search_seg(block);
    add_free_list(block, head);
}
static void remove_seg_list(block_t *block) {
    block_t **head = search_seg(block);
    remove_from_list(block, head);
}
/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}
static void modify_next_prev_state(block_t *block, bool alloc) {
    block_t *next_header = find_next(block);

    word_t word = next_header->header;
    word |= (word_t)(alloc << 1);
    next_header->header = word;
}
static bool extract_prev_alloc(word_t header) {
    return (bool)((header & prev_alloc_mask) >> 1);
}
static bool get_prev_alloc(block_t *block) {
    return extract_prev_alloc(block->header);
}
/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * TODO: Are there any preconditions or postconditions?
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);

    bool status = get_prev_alloc(block);
    block->header = (pack(size, alloc) | ((word_t)status << 1));

    if (!alloc) {
        word_t *footerp = header_to_footer(block);
        *footerp = (pack(size, alloc) | ((word_t)status << 1));
    }
    modify_next_prev_state(block, alloc);
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    word_t *footerp = find_prev_footer(block);

    return footer_to_header(footerp);
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

/**
 * @brief
 *
 * colaescing prev, current, and next free block into one free block to reduce
 * external fragmentation precoditions: colaesing when request more memory and
 * free block postcondition: the mergerd block must be free and in the seglist
 *
 * @param[in] block Address of block
 * @param[in] size size of the block
 * @return    adddree of merged free block
 */
static block_t *coalesce_block(block_t *block, size_t size) {

    // word_t *prev_foot = find_prev_footer(block);

    block_t *next_block = find_next(block);
    bool prev_alloc_status;
    if (block == heap_start) {
        prev_alloc_status = true;
    } else {
        prev_alloc_status = get_prev_alloc(block);
    }

    bool next_alloc_status = get_alloc(next_block);

    if (prev_alloc_status == true && next_alloc_status == true) {
        return block;
    }

    if (prev_alloc_status == true && next_alloc_status == false) {
        size_t merged_size = get_size(block) + get_size(next_block);
        remove_seg_list(next_block);
        remove_seg_list(block);
        write_block(block, merged_size, false);
        add_seg_list(block);
        ////////////attention

        return block;
    }
    block_t *prev_block = find_prev(block);

    if (prev_alloc_status == false && next_alloc_status == true) {

        size_t merged_size = get_size(block) + get_size(prev_block);
        remove_seg_list(block);
        remove_seg_list(prev_block);
        write_block(prev_block, merged_size, false);
        add_seg_list(prev_block);

        return prev_block;
    }

    size_t merged_size =
        get_size(block) + get_size(prev_block) + get_size(next_block);
    remove_seg_list(prev_block);
    remove_seg_list(block);
    remove_seg_list(next_block);
    write_block(prev_block, merged_size, false);
    add_seg_list(prev_block);

    return prev_block;
}

/**
 * @brief extend the heap by given size
 * precodition: There is no approiate free block to be allocated
 * postcodition: a larger size of heap
 *
 * @param[in] size
 * @return the address of the requested the free block
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk((intptr_t)size)) == (void *)-1) {
        return NULL;
    }

    /*
     * TODO: delete or replace this comment once you've thought about it.
     * Think about what bp represents. Why do we write the new block
     * starting one word BEFORE bp, but with the same size that we
     * originally requested?
     */

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false);
    ///
    add_seg_list(block);
    // add_free_list(block);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);

    // Coalesce in case the previous block was free
    block = coalesce_block(block, size);

    return block;
}

/**
 * @brief splite the free portion of the allocated block and add it into seglist
 * precondition: there is a free portion of the block
 * postcondition: the free portion of the block become a block and is added to
 * the list
 *
 * @param[in] block
 * @param[in] asize
 * @return void
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));
    /* TODO: Can you write a precondition about the value of asize? */

    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        write_block(block, asize, true);

        block_next = find_next(block);
        write_block(block_next, block_size - asize, false);
        add_seg_list(block_next);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief find first fit free block thank can be allocated
 * precondition: allocating a memory
 * postition: find the approiated free block
 *
 * @param[in] asize
 * @return the address of the block
 */
static block_t *find_fit(size_t asize) {
    block_t *block;
    block_t *current_head;
    for (size_t i = search_seg_by_size(asize); i < LIST_NUM; i++) {
        current_head = seglist[i];
        for (block = current_head; block != NULL; block = *get_next(block)) {

            if (!(get_alloc(block)) && (asize <= get_size(block))) {
                return block;
            }
        }
    }
    return NULL; // no fit found
}

/**
 * check epi and pro
 */
static bool mm_check_epi_pro_logue(void) {
    word_t *initial_heap = mem_heap_lo();
    if (extract_size(*initial_heap) != 0 ||
        extract_alloc(*initial_heap) == false) {
        return false;
    }

    word_t *epilogue = (word_t *)((char *)mem_heap_hi() - 7);

    if (extract_size(*epilogue) != 0 || extract_alloc(*epilogue) == false) {
        return false;
    }
    return true;
}

/**
 * check alignment
 */
static bool mm_check_alignment(void) {
    block_t *current;
    for (current = heap_start; get_size(current) > 0;
         current = find_next(current)) {
        char *bp = header_to_payload(current);

        if (((word_t)bp % (word_t)16) != 0) {
            return false;
        }
    }
    return true;
}

static bool mm_check_coalescing(void) {
    block_t *current;
    for (current = heap_start; get_size(current) > 0;
         current = find_next(current)) {

        if (get_alloc(current) == false) {
            if (current == heap_start) {
                if (get_alloc(find_next(current)) == false) {
                    return false;

                } else {
                    return true;
                }
            }

            if (get_alloc((footer_to_header(find_prev_footer(current)))) ==
                    false ||
                get_alloc(find_next(current)) == false) {
                return false;
            }
        }
    }
    return true;
}

static bool mm_check_boundaries(void) {
    char *initial_heap = (char *)mem_heap_lo() + 8;
    char *epilogue = ((char *)mem_heap_hi() - 7);
    block_t *current;
    for (current = heap_start; get_size(current) > 0;
         current = find_next(current)) {
        char *bp = (char *)current;

        if ((word_t)bp < (word_t)initial_heap ||
            (word_t)current > (word_t)epilogue) {
            return false;
        }
    }
    return true;
}

static bool mm_check_header_footer(void) {

    for (block_t *current = heap_start; get_size(current) > 0;
         current = find_next(current)) {
        size_t size = get_size(current);
        if (size < min_block_size) {
            return false;
        }

        word_t *footer = header_to_footer(current);
        bool result = get_alloc(current) == extract_alloc(*footer);

        if (!result) {
            return false;
        }
    }
    return true;
}

static bool mm_check_prev_next(void) {
    for (size_t i = 0; i < LIST_NUM; i++) {
        block_t *current = seglist[i];

        while (current != NULL && (*get_next(current)) != NULL) {
            block_t *next = *get_next(current);
            block_t *next_prev = *get_prev(next);

            bool result = next_prev == current;

            if (!result) {
                return false;
            }

            current = next;
        }
    }

    return true;
}

static bool mm_check_pointer_heap(void) {
    block_t *initial_heap = (block_t *)((char *)mem_heap_lo() + 8);
    block_t *epilogue = (block_t *)((char *)mem_heap_hi() - 7);

    for (size_t i = 0; i < LIST_NUM; i++) {
        block_t *current = seglist[i];

        while (current != NULL) {
            block_t *next = *get_next(current);
            block_t *prev = *get_prev(current);

            bool result_prev = (prev == NULL) ||
                               ((prev >= initial_heap) && (prev <= epilogue));
            bool result_next = (next == NULL) ||
                               ((next >= initial_heap) && (next <= epilogue));

            if (!(result_next && result_prev)) {

                return false;
            }

            current = next;
        }
    }
    return true;
}

static bool mm_check_free_count(void) {
    size_t heap_count = 0;
    size_t free_count = 0;
    for (block_t *current = heap_start; get_size(current) > 0;
         current = find_next(current)) {
        if (!get_alloc(current)) {
            heap_count++;
        }
    }

    for (size_t i = 0; i < LIST_NUM; i++) {
        block_t *current = seglist[i];

        while (current != NULL) {
            if (!get_alloc(current)) {
                free_count++;
            }
            current = *get_next(current);
        }
    }

    return heap_count == free_count;
}

static bool mm_check_seglist_range(void) {
    for (size_t i = 0; i < LIST_NUM; i++) {
        block_t *current = seglist[i];
        size_t range_left = 1 << (i + 4);

        size_t range_right = 1 << (i + 5);
        while (current != NULL) {
            if (i == LIST_NUM - 1) {
                bool result = get_size(current) >= MAX_SIZE;
                if (!result) {

                    return false;
                }
            } else {
                size_t size = get_size(current);
                bool result = size > range_left && size <= range_right;

                if (!result) {

                    return false;
                }
            }

            current = *get_next(current);
        }
    }
    return true;
}

/**
 * @brief check heap whether heap is valid without any error
 * check freelist is valid and each of the block is valid
 *
 *
 * @param[in] line
 * @return true if the heap is valid without any error, otherwise false
 */
bool mm_checkheap(int line) {

    // bool check_epi_pro = mm_check_epi_pro_logue();
    bool check_alignment = mm_check_alignment();
    // bool check_coalescing = mm_check_coalescing();
    // bool check_boundaries = mm_check_boundaries();
    // bool check_header_footer = mm_check_header_footer();
    // bool check_prev_next = mm_check_prev_next();
    // bool check_pointer_heap = mm_check_pointer_heap();
    // bool check_free_count = mm_check_free_count();
    // bool check_seglist_range = mm_check_seglist_range();

    // if (!check_epi_pro) {
    //     printf("epi or pro logue error\n");
    // }
    if (!check_alignment) {
        printf("alignment error\n");
    }
    // if (!check_coalescing) {
    //     printf("coalescing error\n");
    // }
    // if (!check_boundaries) {
    //     printf("boundaries error\n");
    // }
    // if (!check_header_footer) {
    //     printf("header_footer error or size error\n");
    // }
    // if (!check_prev_next) {
    //     printf("Pointer error\n");
    // }
    // if (!check_pointer_heap) {
    //     printf("Pointer is not in the heap\n");
    // }

    // if (!check_free_count) {
    //     printf(" free count error\n");
    // }

    // if (!check_seglist_range) {
    //     printf("seglist range error\n");
    // }

    // return check_epi_pro && check_alignment&&
    // check_boundaries&&check_coalescing;
    //
    // return check_epi_pro &&
    return check_alignment;
    //        check_coalescing && check_header_footer && check_pointer_heap &&
    //        check_free_count && check_seglist_range;

    /** TODO: Delete this comment!
     *
     * You will need to write the heap checker yourself.
     * Please keep modularity in mind when you're writing the heap checker!
     *
     * As a filler: one guacamole is equal to 6.02214086 x 10**23 guacas.
     * One might even call it...  the avocado's number.
     *
     * Internal use only: If you mix guacamole on your bibimbap,
     * do you eat it with a pair of chopsticks, or with a spoon?
     */

    dbg_printf("I did not write a heap checker (called at line %d)\n", line);
    return true;
}

/**
 * @brief initialize the heap, prologue and epilogue
 * precodition: initialization
 * postcondition: there is a available heap
 *
 * @param[in] void
 * @return
 */
bool mm_init(void) {

    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }
    for (int i = 0; i < LIST_NUM; i++) {
        seglist[i] = NULL;
    }

    /*
     * TODO: delete or replace this comment once you've thought about it.
     * Think about why we need a heap prologue and epilogue. Why do
     * they correspond to a block footer and header respectively?
     */

    start[0] = pack(0, true);         // Heap prologue (block footer)
    start[1] = (pack(0, true) | 0x2); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    return true;
}

/**
 * @brief Allocate memory from heap, splite and coalesce the approiated block
 * and return porinter of the requested block preconidtion: the heap has
 * available memory size postconditon: return the pointer of the block and
 * maintain the seglist
 *
 * @param[in] size
 * @return pointer of the requested block
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        if (!(mm_init())) {
            dbg_printf("Problem initializing heap. Likely due to sbrk");
            return NULL;
        }
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);
    if (asize < min_block_size) {
        asize = min_block_size;
    }

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Mark block as allocated
    size_t block_size = get_size(block);
    write_block(block, block_size, true);
    remove_seg_list(block);

    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief Free the the allocated memory
 * precodition: the block is allocated
 * postcondition: the allocated block is free
 * @param[in] bp
 * @return void
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false);
    add_seg_list(block);

    // Try to coalesce the block with its neighbors
    coalesce_block(block, size);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief attempts to resize the memory block pointed to by ptr that was
 * previously allocated with a call to malloc or calloc. precondition: the heap
 * has available memory size postconditon: return the pointer of the block and
 * maintain the seglist
 * @param[in] ptr
 * @param[in] size
 * @return
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief allocates the requested memory and sets allocated memory to zero and
 * returns a pointer to it.
 *
 * precondition: the heap has available memory size
 * postconditon: return the pointer of the block and maintain the seglist
 *
 * @param[in] elements
 * @param[in] size
 * @return
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
