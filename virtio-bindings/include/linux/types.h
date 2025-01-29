/* SPDX-License-Identifier: (BSD-3-Clause OR Apache-2.0) */

#pragma once

/* Built-ins avoid the need for <stdint.h> */
typedef __UINT8_TYPE__ __u8;
typedef __UINT16_TYPE__ __u16;
typedef __UINT32_TYPE__ __u32;
typedef __UINT64_TYPE__ __u64;

typedef __u16 __le16;
typedef __u32 __le32;
typedef __u64 __le64;

#define __bitwise /* ignore */
