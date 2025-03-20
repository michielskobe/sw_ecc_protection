/**
 * sw_ecc_protection.c - Software ECC Memory Protection using CRC32 CPU instructions
 *
 * Enhanced version with universal memory protection covering all page allocations.
 */

 #include <linux/module.h>
 #include <linux/kernel.h>
 #include <linux/init.h>
 #include <linux/mm.h>
 #include <linux/mm_types.h>
 #include <linux/slab.h>
 #include <linux/list.h>
 #include <linux/spinlock.h>
 #include <linux/rmap.h>
 #include <linux/highmem.h>
 #include <linux/pagemap.h>
 #include <linux/crypto.h>
 #include <linux/kprobes.h>
 #include <linux/memcontrol.h>
 #include <linux/notifier.h>
 #include <linux/kthread.h>
 #include <linux/delay.h>
 #include <linux/hashtable.h>
  
 #if defined(__aarch64__)
 #include <asm/hwcap.h>
 #include <asm/neon.h>
 /* ARM CRC32 intrinsics */
 #include <arm_acle.h>
 #endif
 
 #if defined(__x86_64__)
 #include <asm/cpufeature.h>
 #endif
  
 MODULE_LICENSE("GPL");
 MODULE_AUTHOR("Lander Van Loock & Kobe Michiels");
 MODULE_DESCRIPTION("Universal Software ECC Memory Protection");
 MODULE_VERSION("0.3");
  
 /* Module parameters */
 static bool enabled = true;
 module_param(enabled, bool, 0644);
 MODULE_PARM_DESC(enabled, "Enable/disable memory protection (default: enabled)");
  
 static bool use_shadow_copy = true;
 module_param(use_shadow_copy, bool, 0644);
 MODULE_PARM_DESC(use_shadow_copy, "Enable/disable shadow copy for recovery (default: enabled)");
 
 static unsigned int verification_interval = 30;
 module_param(verification_interval, uint, 0644);
 MODULE_PARM_DESC(verification_interval, "Background verification interval in seconds (default: 30)");
 
 /* Flag for hardware CRC32 capability */
 static bool hw_crc32_available = false;
 
 /* Hash table to store protected pages */
 #define HASH_BITS 16
 DECLARE_HASHTABLE(protected_pages, HASH_BITS);
 static DEFINE_SPINLOCK(protected_pages_lock);
 
 /* Background verification task */
 static struct task_struct *verification_task = NULL;
 
 /* Protected page structure */
 struct protected_page {
     struct hlist_node hash;     /* Hash table node */
     struct page *page;          /* Pointer to the page */
     u32 crc;                    /* CRC value for the page */
     void *shadow_copy;          /* Shadow copy for recovery */
     unsigned long last_verified;/* Timestamp of last verification */
     atomic_t access_count;      /* Access counter */
 };
 
 /* Statistics */
 static atomic_t total_protected_pages = ATOMIC_INIT(0);
 static atomic_t total_corruptions = ATOMIC_INIT(0);
 static atomic_t total_repairs = ATOMIC_INIT(0);
 static atomic_t total_allocations_intercepted = ATOMIC_INIT(0);
 static atomic_t allocation_failures = ATOMIC_INIT(0);
 
 /* Hardware CRC32 calculation functions */
  
 /**
 * Calculates CRC32 value for a byte using ARM CRC32 instructions
 */
 static inline u32 hw_crc32_u8(u32 crc, u8 data) {
     #if defined(__aarch64__)
         if (hw_crc32_available) {
             return __crc32cb(crc, data);
         }
     #endif
     /* If hardware not available, this will be caught during init */
     return 0;
 }
     
 /**
 * Calculates CRC32 value for a 32-bit word using ARM CRC32 instructions
 */
 static inline u32 hw_crc32_u32(u32 crc, u32 data) {
     #if defined(__aarch64__)
         if (hw_crc32_available) {
             return __crc32cw(crc, data);
         }
     #endif
     /* If hardware not available, this will be caught during init */
     return 0;
 }
     
 /**
 * Calculates CRC32 value for a 64-bit word using ARM CRC32 instructions
 */
 static inline u32 hw_crc32_u64(u32 crc, u64 data) {
     #if defined(__aarch64__)
         if (hw_crc32_available) {
             return __crc32cd(crc, data);
         }
     #endif
     /* If hardware not available, this will be caught during init */
     return 0;
 }
     
 /**
 * Calculates CRC32 for a memory block with maximum hardware acceleration
 */
 static u32 calculate_crc32(const void *data, size_t length) {
    if (hw_crc32_available) {
        /* Initial CRC value (standard for CRC32) */
        u32 crc = 0xFFFFFFFF;
        const unsigned char *buf = data;
        size_t i;
            
        /* Process byte-by-byte until we reach 8-byte alignment */
        while (length && ((uintptr_t)buf & 7)) {
            crc = hw_crc32_u8(crc, *buf++);
            length--;
        }
            
        /* Process 8 bytes at a time for maximum throughput */
        while (length >= 8) {
            crc = hw_crc32_u64(crc, *(u64 *)buf);
            buf += 8;
            length -= 8;
        }
            
        /* Process any remaining bytes */
        while (length--) {
            crc = hw_crc32_u8(crc, *buf++);
        }
        
        /* Final XOR for CRC32 */
        return ~crc;
    } else {
        return 0;
    }   
 }
 
 /**
  * Check for hardware CRC32 support
  */
 static int check_hw_crc32_support(void) {
 #if defined(__aarch64__)
     /* Check if CPU supports CRC32 instructions on ARM64 */
     if (elf_hwcap & HWCAP_CRC32) {
         printk(KERN_INFO "sw_ecc: Hardware CRC32 instructions available\n");
         return 1;
     }
 #elif defined(__x86_64__)
     /* For x86_64, we would check CPUID for SSE4.2 which includes CRC32 */
     if (boot_cpu_has(X86_FEATURE_CRC32)) {
         printk(KERN_INFO "sw_ecc: Hardware CRC32 instructions available (SSE4.2)\n");
         return 1;
     }
 #endif
     printk(KERN_WARNING "sw_ecc: Hardware CRC32 instructions NOT available, using software fallback\n");
     return 0;
 }
 
 /**
  * Find a protected page entry in the hash table
  */
 static struct protected_page *find_protected_page(struct page *page) {
     struct protected_page *p_page;
     unsigned long flags;
     unsigned long key = (unsigned long)page;
     
     spin_lock_irqsave(&protected_pages_lock, flags);
     hash_for_each_possible(protected_pages, p_page, hash, key) {
         if (p_page->page == page) {
             spin_unlock_irqrestore(&protected_pages_lock, flags);
             return p_page;
         }
     }
     spin_unlock_irqrestore(&protected_pages_lock, flags);
     
     return NULL;
 }
 
 /**
  * Create a shadow copy of a page's content
  */
 static void *create_shadow_copy(struct page *page) {
     void *kaddr, *shadow;
     
     if (!use_shadow_copy)
         return NULL;
     
     shadow = kmalloc(PAGE_SIZE, GFP_KERNEL);
     if (!shadow)
         return NULL;
     
     kaddr = kmap_atomic(page);
     if (!kaddr) {
         kfree(shadow);
         return NULL;
     }
     
     memcpy(shadow, kaddr, PAGE_SIZE);
     kunmap_atomic(kaddr);
     
     return shadow;
 }
 
 /**
  * Calculate CRC32 for a page
  */
 static u32 calculate_page_crc(struct page *page) {
     void *kaddr;
     u32 crc;
     
     kaddr = kmap_atomic(page);
     if (!kaddr)
         return 0;
     
     crc = calculate_crc32(kaddr, PAGE_SIZE);
     kunmap_atomic(kaddr);
     
     return crc;
 }
 
 /**
  * Verify the integrity of a page
  * Returns: 1 if corrupted, 0 if intact
  */
 static int verify_page_integrity(struct protected_page *p_page) {
     void *kaddr;
     u32 current_crc;
     int corrupted = 0;
     
     if (!p_page || !p_page->page)
         return 0;
     
     kaddr = kmap_atomic(p_page->page);
     if (!kaddr)
         return 0;
     
     current_crc = calculate_crc32(kaddr, PAGE_SIZE);
     kunmap_atomic(kaddr);
     
     if (current_crc != p_page->crc) {
         printk(KERN_WARNING "sw_ecc: Memory corruption detected in page %p (stored: %08x, current: %08x)\n",
                p_page->page, p_page->crc, current_crc);
         atomic_inc(&total_corruptions);
         corrupted = 1;
     }
     
     return corrupted;
 }
 
 /**
  * Repair a corrupted page from its shadow copy
  */
 static int repair_page(struct protected_page *p_page) {
     void *kaddr;
     int ret = -EINVAL;
     
     if (!p_page || !p_page->page || !p_page->shadow_copy)
         return -EINVAL;
     
     kaddr = kmap_atomic(p_page->page);
     if (!kaddr)
         return -ENOMEM;
     
     memcpy(kaddr, p_page->shadow_copy, PAGE_SIZE);
     kunmap_atomic(kaddr);
     
     p_page->crc = calculate_page_crc(p_page->page);
     
     printk(KERN_INFO "sw_ecc: Page %p repaired from shadow copy\n", p_page->page);
     atomic_inc(&total_repairs);
     
     return 0;
 }
 
 /**
  * Register a page for protection
  */
 static int protect_page(struct page *page) {
     struct protected_page *p_page;
     unsigned long flags;
     
     if (!enabled || !page || PageReserved(page))
         return -EINVAL;
     
     /* Check if page is already protected */
     if (find_protected_page(page))
         return 0;
     
     /* Allocate protected page structure */
     p_page = kmalloc(sizeof(struct protected_page), GFP_KERNEL);
     if (!p_page) {
         atomic_inc(&allocation_failures);
         return -ENOMEM;
     }
     
     /* Initialize protected page */
     p_page->page = page;
     p_page->crc = calculate_page_crc(page);
     p_page->shadow_copy = create_shadow_copy(page);
     p_page->last_verified = jiffies;
     atomic_set(&p_page->access_count, 0);
     
     /* Add to hash table */
     spin_lock_irqsave(&protected_pages_lock, flags);
     hash_add(protected_pages, &p_page->hash, (unsigned long)page);
     spin_unlock_irqrestore(&protected_pages_lock, flags);
     
     atomic_inc(&total_protected_pages);
     
     return 0;
 }
 
 /**
  * Remove protection from a page
  */
 static int unprotect_page(struct page *page) {
     struct protected_page *p_page;
     unsigned long flags;
     
     if (!page)
         return -EINVAL;
     
     p_page = find_protected_page(page);
     if (!p_page)
         return -ENOENT;
     
     /* Remove from hash table */
     spin_lock_irqsave(&protected_pages_lock, flags);
     hash_del(&p_page->hash);
     spin_unlock_irqrestore(&protected_pages_lock, flags);
     
     /* Free shadow copy if allocated */
     if (p_page->shadow_copy)
         kfree(p_page->shadow_copy);
     
     /* Free protected page structure */
     kfree(p_page);
     
     atomic_dec(&total_protected_pages);
     
     return 0;
 }
 
 /**
  * Page fault handler to intercept memory access and verify integrity
  */
 static vm_fault_t sw_ecc_fault_handler(struct vm_fault *vmf) {
     struct page *page;
     struct protected_page *p_page;
     int corrupted;
     
     if (!enabled)
         return VM_FAULT_NOPAGE;
     
     /* Get the page */
     page = vmf->page;
     if (!page)
         return VM_FAULT_NOPAGE;
     
     /* Find the protected page */
     p_page = find_protected_page(page);
     if (!p_page)
         return VM_FAULT_NOPAGE;
     
     /* Update access counter */
     atomic_inc(&p_page->access_count);
     
     /* Verify integrity */
     corrupted = verify_page_integrity(p_page);
     if (corrupted && p_page->shadow_copy) {
         repair_page(p_page);
     }
     
     /* Update CRC */
     p_page->crc = calculate_page_crc(page);
     p_page->last_verified = jiffies;
     
     return VM_FAULT_NOPAGE;
 }
 
 /**
  * Virtual memory operations structure with our fault handler
  */
 static struct vm_operations_struct sw_ecc_vm_ops = {
     .fault = sw_ecc_fault_handler,
 };
 
 /**
  * Kretprobe handler for page allocation
  */
 static int sw_ecc_alloc_pages_handler(struct kretprobe_instance *ri, struct pt_regs *regs) {
     struct page *page;
     
     if (!enabled)
         return 0;
     
     /* Get the allocated page from the return value */
 #ifdef CONFIG_X86_64
     page = (struct page *)regs->ax;
 #elif defined(CONFIG_ARM64)
     page = (struct page *)regs->regs[0];
 #else
     page = NULL;
 #endif
     
     if (!page)
         return 0;
     
     /* Protect the page */
     atomic_inc(&total_allocations_intercepted);
     protect_page(page);
     
     return 0;
 }
 
 /* Kretprobe for intercepting page allocations */
 static struct kretprobe sw_ecc_alloc_pages_probe = {
     .handler = sw_ecc_alloc_pages_handler,
     .maxactive = 20,
 };
 
 /**
  * Kretprobe handler for page freeing
  */
 static int sw_ecc_free_pages_handler(struct kretprobe_instance *ri, struct pt_regs *regs) {
     struct page *page;
     
     if (!enabled)
         return 0;
     
     /* Get the page being freed from the first argument */
 #ifdef CONFIG_X86_64
     page = (struct page *)regs->di;
 #elif defined(CONFIG_ARM64)
     page = (struct page *)regs->regs[0];
 #else
     page = NULL;
 #endif
     
     if (!page)
         return 0;
     
     /* Unprotect the page */
     unprotect_page(page);
     
     return 0;
 }
 
 /* Kretprobe for intercepting page frees */
 static struct kretprobe sw_ecc_free_pages_probe = {
     .handler = sw_ecc_free_pages_handler,
     .maxactive = 20,
 };
 
 /**
  * Background verification thread
  */
 static int sw_ecc_verification_thread(void *data) {
     struct protected_page *p_page;
     int corrupted;
     int bkt;
     unsigned long interval = verification_interval * HZ;
     unsigned long now;
     
     while (!kthread_should_stop()) {
         /* Sleep for a while */
         schedule_timeout_interruptible(interval);
         
         if (!enabled)
             continue;
         
         now = jiffies;
         
         /* Check all protected pages */
         spin_lock(&protected_pages_lock);
         hash_for_each(protected_pages, bkt, p_page, hash) {
             /* Skip recently verified pages */
             if (time_before(now, p_page->last_verified + interval))
                 continue;
             
             /* Verify integrity */
             corrupted = verify_page_integrity(p_page);
             p_page->last_verified = now;
             
             /* Try to repair if corrupted */
             if (corrupted && p_page->shadow_copy) {
                 repair_page(p_page);
             }
         }
         spin_unlock(&protected_pages_lock);
     }
     
     return 0;
 }
 
 /**
  * Sysfs attribute to display module statistics
  */
 static ssize_t sw_ecc_stats_show(struct kobject *kobj, struct kobj_attribute *attr, char *buf) {
     return sprintf(buf, 
                   "Protected pages: %d\n"
                   "Detected corruptions: %d\n"
                   "Successful repairs: %d\n"
                   "Allocations intercepted: %d\n"
                   "Allocation failures: %d\n"
                   "Hardware CRC32: %s\n"
                   "Shadow copy: %s\n"
                   atomic_read(&total_protected_pages),
                   atomic_read(&total_corruptions),
                   atomic_read(&total_repairs),
                   atomic_read(&total_allocations_intercepted),
                   atomic_read(&allocation_failures),
                   hw_crc32_available ? "enabled" : "disabled",
                   use_shadow_copy ? "enabled" : "disabled",);
 }
 
 /**
  * Sysfs attribute to control module settings
  */
 static ssize_t sw_ecc_control_store(struct kobject *kobj, struct kobj_attribute *attr, 
                                     const char *buf, size_t count) {
     int value;
     
     /* Parse command */
     if (strncmp(buf, "enable", 6) == 0) {
         enabled = true;
         printk(KERN_INFO "sw_ecc: Protection enabled\n");
     } else if (strncmp(buf, "disable", 7) == 0) {
         enabled = false;
         printk(KERN_INFO "sw_ecc: Protection disabled\n");
     } else if (sscanf(buf, "interval %d", &value) == 1 && value > 0) {
         verification_interval = value;
         printk(KERN_INFO "sw_ecc: Verification interval set to %d seconds\n", value);
     }
     
     return count;
 }
 
 /* Define sysfs attributes */
 static struct kobj_attribute sw_ecc_stats_attribute = 
     __ATTR(stats, 0444, sw_ecc_stats_show, NULL);
 static struct kobj_attribute sw_ecc_control_attribute = 
     __ATTR(control, 0200, NULL, sw_ecc_control_store);
 
 /* Define attribute groups */
 static struct attribute *sw_ecc_attrs[] = {
     &sw_ecc_stats_attribute.attr,
     &sw_ecc_control_attribute.attr,
     NULL,
 };
 
 static struct attribute_group sw_ecc_attr_group = {
     .attrs = sw_ecc_attrs,
     .name = "sw_ecc",
 };
 
 /* Kobject for sysfs interface */
 static struct kobject *sw_ecc_kobj;
 
 /**
  * Module initialization
  */
 static int __init sw_ecc_init(void) {
     int ret;
     
     /* Initialize the hash table */
     hash_init(protected_pages);
     
     /* Check if hardware CRC32 is available */
     hw_crc32_available = check_hw_crc32_support();
     
     /* Register kretprobes to intercept page allocations/frees */
     sw_ecc_alloc_pages_probe.kp.symbol_name = "alloc_pages";
     ret = register_kretprobe(&sw_ecc_alloc_pages_probe);
     if (ret < 0) {
         printk(KERN_ERR "sw_ecc: Failed to register alloc_pages probe: %d\n", ret);
         return ret;
     }
     
     sw_ecc_free_pages_probe.kp.symbol_name = "__free_pages";
     ret = register_kretprobe(&sw_ecc_free_pages_probe);
     if (ret < 0) {
         printk(KERN_ERR "sw_ecc: Failed to register __free_pages probe: %d\n", ret);
         unregister_kretprobe(&sw_ecc_alloc_pages_probe);
         return ret;
     }
     
     /* Create sysfs entries */
     sw_ecc_kobj = kobject_create_and_add("sw_ecc", kernel_kobj);
     if (!sw_ecc_kobj) {
         printk(KERN_ERR "sw_ecc: Failed to create kobject\n");
         unregister_kretprobe(&sw_ecc_alloc_pages_probe);
         unregister_kretprobe(&sw_ecc_free_pages_probe);
         return -ENOMEM;
     }
     
     ret = sysfs_create_group(sw_ecc_kobj, &sw_ecc_attr_group);
     if (ret) {
         printk(KERN_ERR "sw_ecc: Failed to create sysfs group\n");
         kobject_put(sw_ecc_kobj);
         unregister_kretprobe(&sw_ecc_alloc_pages_probe);
         unregister_kretprobe(&sw_ecc_free_pages_probe);
         return ret;
     }
     
     /* Start background verification thread */
     verification_task = kthread_run(sw_ecc_verification_thread, NULL, "sw_ecc_verify");
     if (IS_ERR(verification_task)) {
         printk(KERN_ERR "sw_ecc: Failed to create verification thread\n");
         sysfs_remove_group(sw_ecc_kobj, &sw_ecc_attr_group);
         kobject_put(sw_ecc_kobj);
         unregister_kretprobe(&sw_ecc_alloc_pages_probe);
         unregister_kretprobe(&sw_ecc_free_pages_probe);
         return PTR_ERR(verification_task);
     }
     
     printk(KERN_INFO "sw_ecc: Universal Software ECC Memory Protection loaded\n");
     
     return 0;
 }
 
 /**
  * Clean up protected pages hash table
  */
 static void cleanup_protected_pages(void) {
     struct protected_page *p_page;
     struct hlist_node *tmp;
     int bkt;
     
     /* Free all protected pages */
     spin_lock(&protected_pages_lock);
     hash_for_each_safe(protected_pages, bkt, tmp, p_page, hash) {
         hash_del(&p_page->hash);
         
         /* Free the shadow copy if allocated */
         if (p_page->shadow_copy)
             kfree(p_page->shadow_copy);
         
         /* Free the protected page structure */
         kfree(p_page);
     }
     spin_unlock(&protected_pages_lock);
 }
 
 /**
  * Module cleanup
  */
 static void __exit sw_ecc_exit(void) {
     /* Stop verification thread */
     if (verification_task)
         kthread_stop(verification_task);
     
     /* Unregister kretprobes */
     unregister_kretprobe(&sw_ecc_alloc_pages_probe);
     unregister_kretprobe(&sw_ecc_free_pages_probe);
     
     /* Clean up protected pages */
     cleanup_protected_pages();
     
     /* Remove sysfs entries */
     sysfs_remove_group(sw_ecc_kobj, &sw_ecc_attr_group);
     kobject_put(sw_ecc_kobj);
     
     printk(KERN_INFO "sw_ecc: Universal Software ECC Memory Protection unloaded\n");
     printk(KERN_INFO "sw_ecc: Final stats - Protected pages: %d, Corruptions: %d, Repairs: %d\n",
            atomic_read(&total_protected_pages), 
            atomic_read(&total_corruptions), 
            atomic_read(&total_repairs));
 }
 
 /* Register module initialization and cleanup functions */
 module_init(sw_ecc_init);
 module_exit(sw_ecc_exit);
 
 /* Export functions for other modules */
 EXPORT_SYMBOL(sw_ecc_fault_handler);