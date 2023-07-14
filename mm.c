/**
 * @file mm.c
 * @brief A 64-bit memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * A 64-bit memory allocator with seglist and free block coalescing.
 *
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
 * @author Junshang Jia <junshanj@andrew.cmu.edu>
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
static const size_t min_block_size = dsize;

/**
 *The minimum size of memory that can request for heap
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 9);

/**
 *  Mask for extract the LSB
 */
static const word_t alloc_mask = 0x1;

/**
 * explain what size_mask is
 * mask for extracting bit excluding 4 bits from LSB
 */
static const word_t size_mask = ~(word_t)0xF;

/** @brief
 * Struct for pointer of next and prev in free block
 */
struct Pointer {
    struct block *next;
    struct block *prev;
};
/** @brief
 * Sturct for minimum 16 bytes free block
 *  8 bytes header + 8 bytes next pointer
 */
struct Miniblock {
    struct block *next;
};

/**
 * union type for payload
 */
union Data {
    /** @brief pointer sturct for free block greater than 16 bytes*/
    struct Pointer pointer;
    /** @brief sturct for minimum free block equal 16 bytes*/
    struct Miniblock miniblock;
    /** @brief random data for allocate*/
    char payload[0];
};

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag + previous allocation flag
     * + previous miniblock flag */
    word_t header;

    /**
     * @brief A pointer to the block payload.
     */
    union Data data;

} block_t;

/** @brief Totall bucket size for seglist*/
#define BUCKET_SIZE 14
/** @brief size great than 32768 will be put in the last index of the list */
#define MAX_SIZE 16384

/** @brief search limit in the list*/
#define SEARCH_LIMIT 10

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

/** @brief the free block size for each seglist bucket is {32,48, 64,
 * 80,96,112,2**(i+1)..... }
 *
 */
static block_t *seglist[BUCKET_SIZE];

/*mask for extract the status of previous allocation bit*/
static const word_t prev_alloc_mask = 0x2;

/*mask for extract the status of previous minimum block*/
static const word_t prev_small_mask = 0x4;

/*minimum free block list*/
static block_t *small_block_start = NULL;

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
 * @param[in] prev_alloc True if the previous block is allocated
 * @param[in] mini_status True if the previous block is minimum 16 bytes block
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc, bool prev_alloc, bool mini_status) {
    word_t word = size;
    if (alloc) {
        word |= (word_t)alloc_mask;
    }
    if (prev_alloc) {
        word |= (word_t)((word_t)prev_alloc << 1);
    }
    if (mini_status) {
        word |= ((word_t)mini_status << 2);
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
    block->header = pack(0, true, false, false);
}

/**
 * @brief Return the the address of the next free block part in the block
 * @param[in] block
 * @return The address of the next free block pointer in the block
 */
static block_t **get_next(block_t *block) {
    return &(block->data.pointer.next);
}

/**
 * @brief Return the the address of the previous free block part in the block
 * @param[in] block
 * @return The address of the previous free block pointer in the block
 */
static block_t **get_prev(block_t *block) {

    return &(block->data.pointer.prev);
}

/**
 * @brief Add free block in the free list
 * @param[in] block the free block
 * @param[in] free_head head of the specific size in the seglist
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
 * @brief remove free block in the free list
 * @param[in] block the free block
 * @param[in] free_head head of the specific size in the seglist
 */
static void remove_from_list(block_t *block, block_t **free_head) {
    /* if the removed block is the head*/
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
        /* if the removed block is in the middle or end of the list*/
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
 * @brief search the bucket based on the size of the block
 * @param[in] block
 * @return the head of the specific size list in the seglist
 */
static block_t **search_seg(block_t *block) {
    size_t size = get_size(block);
    /* if the size greater than maximum size, put it in the last index of the
     * seglist*/
    if (size >= MAX_SIZE) {
        return &seglist[BUCKET_SIZE - 1];
    }
    /* search first five special size of buckets, 32 48,64,80,96*/
    for (size_t i = 0; i < 6; i++) {
        size_t current_size = 32 + (16 * i);
        if (current_size == size) {
            return &seglist[i];
        }
    }

    /* search later buckets size based on the power of 2*/
    for (size_t i = 6; i < BUCKET_SIZE; i++) {

        size_t current_size = 1 << (i + 1);
        if (current_size > size) {

            return &seglist[i - 1];
        }
    }
    dbg_printf("search failed,error\n");
    return NULL;
}
/**
 * @brief search the bucket based on the size
 * @param[in] block
 * @return the head of the specific size list in the seglist
 */
static size_t search_seg_by_size(size_t size) {
    if (size > MAX_SIZE) {
        return BUCKET_SIZE - 1;
    }
    for (size_t i = 0; i < 6; i++) {
        size_t current_size = 32 + (16 * i);
        if (current_size == size) {
            return i;
        }
    }

    for (size_t i = 6; i < BUCKET_SIZE; i++) {

        size_t current_size = 1 << (i + 1);
        if (current_size > size) {

            return i - 1;
        }
    }
    dbg_printf("search failed,error\n");
    return 1;
}

/**
 * @brief add free block in the segist
 * @param[in] block the free block
 */
static void add_seg_list(block_t *block) {
    block_t **head = search_seg(block);
    add_free_list(block, head);
}
/**
 * @brief remove free block in the segist
 * @param[in] block the free block
 */
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

/**
 * @brief The function modifies the next block's header state by updating its
 * allocation status and mini status.
 *
 * @param block A pointer to a block structure.
 * @param alloc The "alloc" parameter is a boolean value that indicates whether
 * the block is being allocated or deallocated. If "alloc" is true, it means the
 * block is being allocated, and if it is false, it means the block is being
 * deallocated.
 * @param mini_status The `mini_status` parameter is a boolean value that
 * represents the status of the block in a mini heap. It indicates whether the
 * block is a mini block or not.
 */
static void modify_next_prev_state(block_t *block, bool alloc,
                                   bool mini_status) {
    block_t *next_header = find_next(block);

    next_header->header =
        pack(get_size(next_header), get_alloc(next_header), alloc, mini_status);
}
/**
 * The function extracts the previous allocation status from a given header.
 *
 * @param header The `header` parameter is a `word_t` type, which is likely an
 * unsigned integer type used to store a memory block header.
 *
 * @return a boolean value.
 */
static bool extract_prev_alloc(word_t header) {
    return (bool)((header & prev_alloc_mask) >> 1);
}
/**
 * @brief returns the value of the "prev_alloc" field in the header of a given
 * block.
 *
 * @param block The parameter "block" is a pointer to a structure of type
 * "block_t".
 *
 * @return True if previous is allocated
 */
static bool get_prev_alloc(block_t *block) {
    return extract_prev_alloc(block->header);
}
/**
 * @brief The function extracts the value of the previous minimum block
 * allocation status from a given header.
 *
 * @param header
 *
 * @return True if previous block is mini block
 */
static bool extract_prev_small(word_t header) {
    return (bool)((header & prev_small_mask) >> 2);
}

/**
 * @brief the value of the "prev_small" field in the header of a given
 * block.
 *
 * @param block
 *
 * @return True if previous block is mini block
 */
static bool get_prev_small(block_t *block) {
    return extract_prev_small(block->header);
}

/**
 * @brief The function writes the header and footer of a block, and modifies the
 * next and previous block's allocation status.
 *
 * @param block A pointer to a block_t structure, which represents a memory
 * block.
 * @param size The size parameter represents the size of the block in bytes. It
 * is used to set the size field in the block's header and footer.
 * @param alloc A boolean value indicating whether the block is allocated or
 * not.
 * @param prev_alloc The "prev_alloc" parameter is a boolean value that
 * indicates whether the previous block in the memory heap is allocated or not.
 * It is used to set the "prev_alloc" field in the header of the current block.
 * @param mini_status The parameter "mini_status" is a boolean value that
 * indicates whether the previous block is a mini block or not.
 */
static void write_block(block_t *block, size_t size, bool alloc,
                        bool prev_alloc, bool mini_status) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);

    block->header = pack(size, alloc, prev_alloc, mini_status);
    /*allocated block does not contain footer*/
    if (!alloc && size != min_block_size) {

        word_t *footerp = header_to_footer(block);
        *footerp = pack(size, alloc, prev_alloc, mini_status);
    }
    bool status = size == min_block_size;
    modify_next_prev_state(block, alloc, status);
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
 * @brief returns a pointer to the previous mini block in memory.
 *
 * @param block A pointer to a block_t structure.
 *
 * @return a pointer to a block_t structure.
 */
static block_t *find_prev_small(block_t *block) {
    return (block_t *)(&(block->header) - 2);
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

/**
 * @brief removes a specific block from a singly linked list called
 * small_block_start.
 *
 * @param block
 *
 */
static void remove_small_list(block_t *block) {
    if (block == small_block_start) {
        block_t *next = block->data.miniblock.next;
        if (next != NULL) {
            block->data.miniblock.next = NULL;
            small_block_start = next;

        } else {
            small_block_start = NULL;
        }
    } else {
        block_t *prev = NULL;
        block_t *current = small_block_start;

        while (current != NULL) {
            if (current == block) {
                block_t *next = current->data.miniblock.next;
                prev->data.miniblock.next = next;
                current->data.miniblock.next = NULL;
                return;
            }
            prev = current;
            current = current->data.miniblock.next;
        }
    }
}

/**
 * @brief add a specific block from a singly linked list called
 * small_block_start.
 *
 * @param block
 *
 */
static void add_small_list(block_t *block) {
    block->data.miniblock.next = NULL;
    if (small_block_start == NULL) {
        small_block_start = block;
    } else {
        block->data.miniblock.next = small_block_start;
        small_block_start = block;
    }
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

    block_t *next_block = find_next(block);

    bool prev_alloc_status = get_prev_alloc(block);

    bool next_alloc_status = get_alloc(next_block);

    /* The above code is checking the allocation status of the previous and next
    blocks. If both blocks are already allocated, it checks the size of the
    current block. If the size is equal to the minimum block size, it adds the
    block to a small list. Otherwise, it adds the block to a segmented list.
    Finally, it returns the block. */
    if (prev_alloc_status == true && next_alloc_status == true) {
        if (size == min_block_size) {
            add_small_list(block);

        } else {
            add_seg_list(block);
        }
        return block;
    }

    /* The above code is checking the allocation status of the previous and next
    blocks. If the previous block is allocated and the next block is not
    allocated, it merges the current block with the next block. It then updates
    the size, allocation status, and previous allocation status of the merged
    block. Finally, it adds the merged block to the appropriate list (either the
    small list or the segment list) and returns the merged block. */
    if (prev_alloc_status == true && next_alloc_status == false) {
        size_t merged_size = get_size(block) + get_size(next_block);
        if (get_size(next_block) == min_block_size) {
            remove_small_list(next_block);
        } else {
            remove_seg_list(next_block);
        }
        bool pre_alloc = get_prev_alloc(block);
        bool mini_status = get_prev_small(block);
        write_block(block, merged_size, false, pre_alloc, mini_status);
        add_seg_list(block);

        return block;
    }
    /* The above code is checking if the previous block is small or not. If the
    previous block is small, it finds the previous small block. Otherwise, it
    finds the previous block. */
    bool is_prev_small = get_prev_small(block);
    block_t *prev_block;
    if (is_prev_small) {
        prev_block = find_prev_small(block);
    } else {
        prev_block = find_prev(block);
    }

    /* The above code is checking the allocation status of the previous and next
    blocks. If the previous block is not allocated and the next block is
    allocated, it merges the current block with the previous block. It then
    updates the size, allocation status, and previous allocation status of the
    merged block. Finally, it adds the merged block to the appropriate list
    (either small list or segment list) and returns the merged block. */
    if (prev_alloc_status == false && next_alloc_status == true) {

        size_t merged_size = get_size(block) + get_size(prev_block);
        if (is_prev_small) {
            remove_small_list(prev_block);

        } else {
            remove_seg_list(prev_block);
        }
        bool pre_alloc = get_prev_alloc(prev_block);
        bool mini_status = get_prev_small(prev_block);

        write_block(prev_block, merged_size, false, pre_alloc, mini_status);
        add_seg_list(prev_block);

        return prev_block;
    }

    /* The above code is merging three blocks together if previous, next and
    current block is free, and updating the necessary data structures. It
    calculates the size of the merged block and removes the previous and next
    blocks from their respective lists. It then checks if the next block has a
    size equal to the minimum block size and removes it from the small list if
    true. It retrieves the allocation and small status of the previous block and
    writes the merged block with the updated data. Finally, it adds the merged
    block to the segment list and returns it. */
    size_t merged_size =
        get_size(block) + get_size(prev_block) + get_size(next_block);
    if (is_prev_small) {
        remove_small_list(prev_block);

    } else {
        remove_seg_list(prev_block);
    }
    if (get_size(next_block) == min_block_size) {
        remove_small_list(next_block);
    } else {
        remove_seg_list(next_block);
    }
    bool pre_alloc = get_prev_alloc(prev_block);
    bool mini_status = get_prev_small(prev_block);

    write_block(prev_block, merged_size, false, pre_alloc, mini_status);
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

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);

    if (block == heap_start) {
        write_block(block, size, false, true, false);

    } else {
        write_block(block, size, false, get_prev_alloc(block),
                    get_prev_small(block));
    }

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

    size_t block_size = get_size(block);
    /*splite block if the splited block has at leas minimum size and add it to
     * the seglist*/
    if ((block_size - asize) >= min_block_size) {

        block_t *block_next;
        write_block(block, asize, true, get_prev_alloc(block),
                    get_prev_small(block));
        bool is_miniblock = asize == min_block_size;

        block_next = find_next(block);
        write_block(block_next, block_size - asize, false, true, is_miniblock);
        /* if the splited block is the mini block, add the splited block in to
         * small_block_start list, otherwise add it to seglist*/
        if ((block_size - asize) == min_block_size) {
            add_small_list(block_next);
        } else {
            add_seg_list(block_next);
        }
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
    block_t *selected = NULL;
    block_t *block = NULL;
    block_t *current_head;
    /*find fit block from seglist based on the size of block*/
    for (size_t i = search_seg_by_size(asize); i < BUCKET_SIZE; i++) {
        /*get the head of specific size in seglist*/
        current_head = seglist[i];
        size_t count = 0;
        /* linear search in the list but only search top 10 element, and get the
         * minimum size of block that meet the requirment, which improve
         * throughtput*/
        for (block = current_head; block != NULL && count < SEARCH_LIMIT;
             block = *get_next(block)) {

            if (!(get_alloc(block)) && (asize <= get_size(block))) {
                if (selected == NULL) {
                    selected = block;
                } else {
                    if (get_size(block) < get_size(selected)) {
                        selected = block;
                    }
                }
            }
            count++;
        }
        if (selected != NULL) {
            break;
        }
    }
    return selected; // no fit found
}

/**
 * @brief  function checks if the initial and final blocks of the heap are
 * correctly formatted.
 *
 * @return a boolean value.
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
 * @brief The function checks if the memory blocks in the heap are aligned on a
 * 16-byte boundary.
 *
 * @return The function `mm_check_alignment` returns a boolean value.
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

/**
 * @brief function checks if coalescing is correctly implemented in the memory
 * management system.
 *
 * @return a boolean value. If all the conditions in the function are satisfied,
 * it will return true. Otherwise, it will return false.
 */
static bool mm_check_coalescing(void) {
    block_t *current;
    for (current = heap_start; get_size(current) > 0;
         current = find_next(current)) {

        if (get_alloc(current) == false) {
            if (current == heap_start) {
                if (get_alloc(find_next(current)) == false) {
                    return false;
                }
            }

            if (get_prev_alloc(current) == false ||
                get_alloc(find_next(current)) == false) {
                return false;
            }
        }
    }
    return true;
}

/**
 * @brief  function `mm_check_boundaries` checks if the boundaries of the heap
 * are within the expected range.
 *
 * @return a boolean value.
 */
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

/**
 * @brief The function `mm_check_header_footer` checks if the headers and
 * footers of all blocks in the heap are consistent.
 *
 * @return a boolean value. If all the header and footer pairs in the heap are
 * valid, the function will return true. Otherwise, it will return false.
 */
static bool mm_check_header_footer(void) {

    for (block_t *current = heap_start; get_size(current) > 0;
         current = find_next(current)) {
        if (!get_alloc(current)) {
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
    }
    return true;
}

/**
 * @brief function `mm_check_prev_next` checks if the previous and next pointers
 * of each block in the `seglist` are correctly set.
 *
 * @return a boolean value. If all the previous and next pointers in the seglist
 * are correctly linked, the function will return true. Otherwise, it will
 * return false.
 */
static bool mm_check_prev_next(void) {
    for (size_t i = 0; i < BUCKET_SIZE; i++) {
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

/**
 * @brief function `mm_check_pointer_heap` checks if all pointers in the heap
 * are valid.
 *
 * @return a boolean value. It returns true if all the pointers in the heap are
 * within the valid range (between initial_heap and epilogue) and false
 * otherwise.
 */
static bool mm_check_pointer_heap(void) {
    block_t *initial_heap = (block_t *)((char *)mem_heap_lo() + 8);
    block_t *epilogue = (block_t *)((char *)mem_heap_hi() - 7);

    for (size_t i = 0; i < BUCKET_SIZE; i++) {
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

    for (block_t *current = small_block_start; current != NULL;
         current = current->data.miniblock.next) {

        bool result_next_mini =
            (current >= initial_heap) && (current <= epilogue);
        if (!result_next_mini) {
            return false;
        }
    }
    return true;
}

/**
 * @brief The function `mm_check_free_count` checks if the number of free blocks
 * in the heap is equal to the number of free blocks in the segregated free
 * lists and small block list.
 *
 * @return a boolean value.
 */
static bool mm_check_free_count(void) {
    size_t heap_count = 0;
    size_t free_count = 0;
    for (block_t *current = heap_start; get_size(current) > 0;
         current = find_next(current)) {
        if (!get_alloc(current)) {
            heap_count++;
        }
    }

    for (size_t i = 0; i < BUCKET_SIZE; i++) {
        block_t *current = seglist[i];

        while (current != NULL) {

            free_count++;

            current = *get_next(current);
        }
    }
    for (block_t *current = small_block_start; current != NULL;
         current = current->data.miniblock.next) {
        free_count++;
    }

    return heap_count == free_count;
}

/**
 * @brief The function `mm_check_seglist_range` checks if the sizes of blocks in
 * the seglist are within the expected range for each bucket.
 *
 * @return a boolean value.
 */
static bool mm_check_seglist_range(void) {

    for (size_t i = 0; i < 6; i++) {
        block_t *current = seglist[i];
        size_t range_left = 32 + 16 * i;

        size_t range_right = 32 + 16 * (i + 1);
        while (current != NULL) {

            size_t size = get_size(current);
            bool result = size >= range_left && size < range_right;

            if (!result) {

                return false;
            }

            current = *get_next(current);
        }
    }
    for (size_t i = 6; i < BUCKET_SIZE; i++) {
        block_t *current = seglist[i];
        size_t range_left = 1 << (i + 1);

        size_t range_right = 1 << (i + 2);
        while (current != NULL) {
            if (i == BUCKET_SIZE - 1) {
                bool result = get_size(current) >= MAX_SIZE;
                if (!result) {

                    return false;
                }
            } else {
                size_t size = get_size(current);
                bool result = size >= range_left && size < range_right;

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

    bool check_epi_pro = mm_check_epi_pro_logue();
    bool check_alignment = mm_check_alignment();
    bool check_coalescing = mm_check_coalescing();
    bool check_boundaries = mm_check_boundaries();
    bool check_header_footer = mm_check_header_footer();
    bool check_prev_next = mm_check_prev_next();
    bool check_pointer_heap = mm_check_pointer_heap();
    bool check_free_count = mm_check_free_count();
    bool check_seglist_range = mm_check_seglist_range();

    if (!check_epi_pro) {
        dbg_printf("epi or pro logue error\n");
    }
    if (!check_alignment) {
        dbg_printf("alignment error\n");
    }
    if (!check_coalescing) {
        dbg_printf("coalescing error\n");
    }
    if (!check_boundaries) {
        dbg_printf("boundaries error\n");
    }
    if (!check_header_footer) {
        dbg_printf("header_footer error or size error\n");
    }
    if (!check_prev_next) {
        dbg_printf("Pointer error\n");
    }
    if (!check_pointer_heap) {
        dbg_printf("Pointer is not in the heap\n");
    }

    if (!check_free_count) {
        dbg_printf(" free count error\n");
    }

    if (!check_seglist_range) {
        dbg_printf("seglist range error\n");
    }
    return check_epi_pro && check_alignment && check_coalescing &&
           check_boundaries && check_header_footer && check_prev_next &&
           check_pointer_heap && check_free_count && check_seglist_range;
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
    for (int i = 0; i < BUCKET_SIZE; i++) {
        seglist[i] = NULL;
    }

    start[0] = pack(0, true, true, false); // Heap prologue (block footer)
    start[1] = pack(0, true, true, false); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);
    small_block_start = NULL;

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

    if (asize == min_block_size && small_block_start != NULL) {

        block = small_block_start;

    } else {
        // Search the free list for a fit
        block = find_fit(asize);
    }

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
    write_block(block, block_size, true, get_prev_alloc(block),
                get_prev_small(block));

    if (asize == min_block_size && small_block_start != NULL) {
        remove_small_list(block);
    } else {
        remove_seg_list(block);

        // Try to split the block if too large
    }
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

    write_block(block, size, false, get_prev_alloc(block),
                get_prev_small(block));

    // Mark the block as free

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
