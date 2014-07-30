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

package javax.microedition.lcdui;

import com.sun.mmedia.MIDPVideoPainter;
import com.sun.mmedia.MMHelper;
import java.util.Vector;

import com.sun.midp.chameleon.MIDPWindow;


/**
 * This is a helper class to communicate between the LCDUI canvas and
 * the MMAPI video players. 
 */
final class MMHelperImpl extends MMHelper {

    private static MMHelperImpl instance = null;
    
    /**
     * Single use constructor. Cannot be instantiated twice. The instance
     * object is held by Canvas as well as MIDPVideoPainter implementation.
     */
    public MMHelperImpl() {
        if (instance != null) {
            throw new RuntimeException("Cannot instantiate MMHelperImpl twice");
        }
        MMHelper.setMMHelper(this);
        instance = this;
    }

    /**
     * Returns the only instance of this class.
     * @return the instance of this class
     */
    static MMHelperImpl getInstance() {
        return instance;
    }

    /**
     * Informs the player to draw into Graphics <code>g</code>
     *
     * @param video The video player which should be repainted.
     * @param g The graphics object to pass to the video player.
     */
    synchronized void paintVideo(Object video, Graphics g) {
        MIDPVideoPainter vp = (MIDPVideoPainter)video;
        vp.paintVideo(g);
    }
    
    /**
     * Notify video renderers that canvas becomes visible.
     * @param video The video painter which is shown.
     */
    synchronized void showVideo(Object video) {
        MIDPVideoPainter vp = (MIDPVideoPainter)video;
        vp.showVideo();
    }

    /**
     * Notify video renderers that canvas becomes invisible.
     * @param video The video painter which is hidden.
     */
    synchronized void hideVideo(Object video) {
        MIDPVideoPainter vp = (MIDPVideoPainter)video;
        vp.hideVideo();
    }

    /****************************************************************
     * MMHelper implementation
     ****************************************************************/

    /**
     * Registers a video control (which implements MIDPVideoPainter) with
     * the corresponding Canvas where the video is to show up.
     */
    public void registerPlayer(Canvas c, MIDPVideoPainter vp) {
        ((CanvasLFImpl)c.canvasLF).addEmbeddedVideo(vp);
    }

    /**
     * Unregisters a video control so that it doesn't get paint callbacks
     * anymore after the player is closed. This also reduces load on the
     * Canvas repaint mechanism.
     */
    public synchronized void unregisterPlayer(Canvas c, MIDPVideoPainter vp) {
        ((CanvasLFImpl)c.canvasLF).removeEmbeddedVideo(vp);
    }

    /**
     * Get Display being used for Item painting. Platform-dependent.
     */
    public Display getDisplayFor(Item item) {
        if (item.owner == null)
            return null;

        return item.owner.getLF().lGetCurrentDisplay();
    }

    /**
     * Get Display being used for painting of given Displayable. Platform-dependent.
     */
    public Display getDisplayFor(Displayable displayable) {
        return displayable.getLF().lGetCurrentDisplay();
    }

    /**
     * Get width of given display.
     * @param display
     * @return number of pixels Display occupies horizontally
     */
    public int getDisplayWidth(Display display) {
        int res =  display != null ?
            display.getDisplayWidth() :
            Display.getPrimaryDisplayWidth();
        return res;
    }

    /**
     * Get height of given display.
     * @param display
     * @return number of pixels Display occupies vertically
     */
    public int getDisplayHeight(Display display) {
        int res = display != null ?
            display.getDisplayHeight() :
            Display.getPrimaryDisplayHeight();
        return res;
    }

    /**
     * Is current Display (playing video) overlapped by system layers
     */
    public boolean isDisplayOverlapped(Graphics g) {
        boolean isOverlapped = false;

        Object creator = g.getCreator();
        if (creator != null) {
            if (creator instanceof Display) {
                MIDPWindow window = ((Display)creator).getWindow();
                isOverlapped = window.systemMenuUp();
            }
        }

        return isOverlapped;
    }

}
