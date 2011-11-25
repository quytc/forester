/*
 * Copyright (C) 2011 Kamil Dudka <kdudka@redhat.com>
 *
 * This file is part of predator.
 *
 * predator is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * any later version.
 *
 * predator is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with predator.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifndef H_GUARD_INTRANGE_H
#define H_GUARD_INTRANGE_H

#include "config.h"

namespace IR {

typedef signed long TInt;

extern const TInt Int0;
extern const TInt Int1;
extern const TInt IntMin;
extern const TInt IntMax;

/// a closed interval over integral domain
struct Range {
    TInt        lo;         ///< lower bound of the interval (included)
    TInt        hi;         ///< upper bound of the interval (included)

    // NOTE: there is no constructor, becase we put Range to unions
};

inline Range rngFromNum(TInt num) {
    Range rng;
    rng.lo = num;
    rng.hi = num;
    return rng;
}

extern const Range FullRange;

/// this does nothing unless running a debug build
void chkRange(const Range &rng);

inline bool operator==(const Range &a, const Range &b) {
    return (a.lo == b.lo)
        && (a.hi == b.hi);
}

inline bool operator!=(const Range &a, const Range &b) {
    return !operator==(a, b);
}

/// invert polarity of the number
TInt invertInt(const TInt);

/// invert polarity of the range
inline Range operator-(Range rng) {
    const TInt hi = invertInt(rng.lo);
    rng.lo = invertInt(rng.hi);
    rng.hi = hi;

    return rng;
}

/// add another range, but preserve boundary values if already reached
Range& operator+=(Range &rng, const Range &other);

/// multiply by another range, but preserve boundary values if already reached
Range& operator*=(Range &rng, const Range &other);

/// subtract another range, but preserve boundary values if already reached
inline Range& operator-=(Range &rng, const Range &other) {
    rng += (-other);
    return rng;
}

inline Range operator+(Range rng, const Range &other) {
    rng += other;
    return rng;
}

inline Range operator*(Range rng, const Range &other) {
    rng *= other;
    return rng;
}

inline Range operator-(Range rng, const Range &other) {
    rng -= other;
    return rng;
}

/// true if the small range is inside the big one (sharing endpoints is fine)
bool isCovered(const Range &small, const Range &big);

/// return true if the range contain exactly one number; break if no one at all
bool isSingular(const Range &);

/// return the count of integral numbers that beTInt the given range
TInt widthOf(const Range &);

} // namespace IR

#endif /* H_GUARD_INTRANGE_H */
