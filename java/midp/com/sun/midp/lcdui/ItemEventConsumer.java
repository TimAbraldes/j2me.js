/*
 *   
 *
 * Copyright  1990-2009 Sun Microsystems, Inc. All Rights Reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License version
 * 2 only, as published by the Free Software Foundation.
 * 
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * General Public License version 2 for more details (a copy is
 * included at /legal/license.txt).
 * 
 * You should have received a copy of the GNU General Public License
 * version 2 along with this work; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
 * 02110-1301 USA
 * 
 * Please contact Sun Microsystems, Inc., 4150 Network Circle, Santa
 * Clara, CA 95054 or visit www.sun.com if you need additional
 * information or have any questions.
 */

package com.sun.midp.lcdui;

import javax.microedition.lcdui.CustomItem;
import javax.microedition.lcdui.Display;
import javax.microedition.lcdui.Displayable;
import javax.microedition.lcdui.Image;
import javax.microedition.lcdui.Item;

/**
 * This I/F processes display events that are not associated directly 
 * with an instance specific DisplayEventConsumer target 
 * (associated with a particular Display).
 * These are Item-related events processed by static Display methods.
 *
 * This I/F is implemented only by 
 * javax.microedition.lcdui.DisplayEventHandlerImpl isolate-wide singleton.
 *
 */
public interface ItemEventConsumer {

    /*
     * ITEM EVENTS - not associated with a particular Display.
     *               Now generated by DisplayEventProducer. 
     *
     * ITEM_CHANGED/STATE_CHANGE
     * ITEM_CHANGED/SIZE_REFRESH
     * ITEM_CHANGED/MAKE_VISIBLE
     */

    /**
     * Called by event delivery to notify an ItemStateChangeListener
     * of a change in an item
     *
     * @param src the Item which has changed
     */
    void handleItemStateChangeEvent(Item src);

    /**
     * Called by event delivery to refresh the size information
     * of a CustomItem.
     *
     * @param src the CustomItem whose size information is to be updated
     */
    void handleItemSizeRefreshEvent(CustomItem src);
}
