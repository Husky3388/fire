// Jason Thai
// CMPS 3480
// Project - Fire

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <X11/Xlib.h>
#include <X11/keysym.h>
#include <unistd.h>
#include <cstdlib>
#include <ctime>
#include <cstring>
#include <cmath>
#include <GL/glx.h>
#include <X11/extensions/Xdbe.h>
#include <string>
#include <iostream>
using namespace std;

//--------------------
//XWindows vaariables
Display *dpy;
Window win;
GC gc;
XdbeBackBuffer backBuffer;
XdbeSwapInfo swapInfo;
//--------------------

struct Vec
{
    float x, y, z;
};

const int cells = 100;
struct Grid
{
    int size;
    int column[cells];
    int row[cells];
};

#define MAX_POINTS 400
struct Global {
    int xres, yres;
    int done;
    int n;
    bool control;

    bool bubbler;
    int lastMouse[2];
    int mouseMoved[2];
    int mouseGrid[2];

    Grid grid;
    bool drawGrid;

    bool fluid;

    Global() {
        //constructor
        xres = 1000;
        yres = 1000;
        done = 0;
        n = 0;
        control = false;
        bubbler = false;
        drawGrid = false;
        fluid = false;
    }
} g;
//-------------------
//function prototypes
void initXwindows();
void cleanupXwindows();
void checkResize(XEvent *e);
void checkMouse(XEvent *e);
void checkKeys(XEvent *e);
void physics(Global *g);
void render();
void clearScreen();

void initGrid();
void checkGrid(Global *g);

static int N = 100;
static const int size = (N+2) * (N+2);
static float *u = new float[size];
static float *v = new float[size];
static float *u_prev = new float[size];
static float *v_prev = new float[size];
static float *dens = new float[size];
static float *dens_prev = new float[size];
static float h = 1/N;
static float visc = 1.0;
static float dt = 1.0;
static float diff = 1.0;
#define IX(i,j) ((i)+(N+2)*(j))
#define SWAP(x0,x) {float *tmp=x0;x0=x;x=tmp;}

void set_bnd(int N, int b, float *x)
{
    for(int i = 1; i <= N; i++) 
    {
        x[IX(0  ,i)] = b==1 ? -x[IX(1,i)] : x[IX(1,i)]; 
        x[IX(N+1,i)] = b==1 ? -x[IX(N,i)] : x[IX(N,i)];
        x[IX(i  ,0)] = b==2 ? -x[IX(i,1)] : x[IX(i,1)];
        x[IX(i,N+1)] = b==2 ? -x[IX(i,N)] : x[IX(i,N)];
    }
    x[IX(0  ,0  )] = 0.5*(x[IX(1,0  )] + x[IX(0 ,1 )]); 
    x[IX(0  ,N+1)] = 0.5*(x[IX(1,N+1)] + x[IX(0 ,N )]); 
    x[IX(N+1,0  )] = 0.5*(x[IX(N,0  )] + x[IX(N+1,1)]); 
    x[IX(N+1,N+1)] = 0.5*(x[IX(N,N+1)] + x[IX(N+1,N)]);
}

void project(int N, float *u, float *v, float *p, float *div)
{
    float h;
    h = 1.0/N;
    for(int i = 1; i <= N; i++) 
    {
        for(int j = 1; j <= N; j++) 
        {
            div[IX(i,j)] = -0.5*h*(u[IX(i+1,j)]-u[IX(i-1,j)]+
                    v[IX(i,j+1)]-v[IX(i,j-1)]);
            p[IX(i,j)] = 0;
        }
    }
    set_bnd(N, 0, div); 
    set_bnd(N, 0, p);

    for(int k = 0; k < 20; k++) 
    {
        for(int i = 1; i <= N; i++) 
        {
            for(int j = 1; j <= N; j++) 
            {
                p[IX(i,j)] = (div[IX(i,j)]+p[IX(i-1,j)]+p[IX(i+1,j)]+
                        p[IX(i,j-1)] + p[IX(i,j+1)]) / 4;
            }
        }
        set_bnd(N, 0, p);
    }

    for(int i = 1; i <= N; i++) 
    {
        for(int j = 1; j <= N; j++) 
        {
            u[IX(i,j)] -= 0.5*(p[IX(i+1,j)]-p[IX(i-1,j)])/h;
            v[IX(i,j)] -= 0.5*(p[IX(i,j+1)]-p[IX(i,j-1)])/h;
        }
    }
    set_bnd(N, 1, u); 
    set_bnd(N, 2, v);
}

void add_source(int N, float *x, float *s, float dt)
{
    int size = (N+2)*(N+2);
    for(int i = 0; i < size; i++)
        x[i] += dt*s[i]; 
}

void diffuse(int N, int b, float *x, float *x0, float diff, float dt)
{
    float a = dt*diff*N*N;
    for(int k = 0; k < 20; k++) 
    {
        for(int i = 1; i <= N; i++) 
        {
            for(int j = 1; j <= N; j++) 
            {
                x[IX(i,j)] = (x0[IX(i,j)] + a*(x[IX(i-1,j)]+x[IX(i+1,j)]+
                            x[IX(i,j-1)] + x[IX(i,j+1)])) / (1+4*a);
            } 
        }
        set_bnd(N, b, x);
    }
}

void advect(int N, int b, float *d, float *d0, float *u, float *v, float dt)
{
    int i0, j0, i1, j1;
    float x, y, s0, t0, s1, t1, dt0;
    dt0 = dt*N;
    for(int i = 1; i <= N; i++) 
    {
        for(int j = 1; j <= N; j++) 
        {
            x = i-dt0*u[IX(i,j)]; 
            y = j-dt0*v[IX(i,j)];
            if(x < 0.5) 
                x = 0.5; 
            if(x > N+0.5) 
                x = N + 0.5; 
            i0 = (int)x; 
            i1 = i0+1;

            if(y < 0.5) 
                y = 0.5; 
            if(y > N + 0.5) 
                y = N + 0.5; 
            j0 = (int)y; 
            j1 = j0+1; 

            s1 = x-i0; 
            s0 = 1-s1; 
            t1 = y-j0; 
            t0 = 1-t1;

            d[IX(i,j)] = s0 * (t0 * d0[IX(i0,j0)] + t1 * d0[IX(i0,j1)]) +
                s1 * (t0 * d0[IX(i1,j0)] + t1 * d0[IX(i1,j1)]);
        } 
    }
    set_bnd(N, b, d); 
}

void dens_step(int N, float *x, float *x0, float *u, float *v, float diff, float dt)
{
    add_source(N, x, x0, dt);

    SWAP(x0, x); 
    diffuse(N, 0, x, x0, diff, dt); 

    SWAP(x0, x); 
    advect(N, 0, x, x0, u, v, dt);
}

void vel_step(int N, float *u, float *v, float *u0, float *v0,
        float visc, float dt)
{
    add_source(N, u, u0, dt); 
    add_source(N, v, v0, dt);

    SWAP(u0, u); 
    diffuse(N, 1, u, u0, visc, dt);

    SWAP(v0, v); 
    diffuse(N, 2, v, v0, visc, dt);

    project(N, u, v, u0, v0);

    SWAP(u0, u); 
    SWAP(v0, v);

    advect(N, 1, u, u0, u0, v0, dt); 
    advect(N, 2, v, v0, u0, v0, dt);

    project(N, u, v, u0, v0);
}

int main()
{
    initGrid();
    srand((unsigned)time(NULL));
    initXwindows();
    while (!g.done) {
        //Check the event queue
        while (XPending(dpy)) {
            //Handle evemts one-by-one
            XEvent e;
            XNextEvent(dpy, &e);
            checkResize(&e);
            checkMouse(&e);
            checkKeys(&e);
        }
        clearScreen();
        physics(&g);

        ///////////////////////////////////////////////////////
        checkGrid(&g); 
        vel_step(N, u, v, u_prev, v_prev, visc, dt);
        dens_step(N, dens, dens_prev, u , v, diff, dt);
        render(); 
        ///////////////////////////////////////////////////////

        XdbeSwapBuffers(dpy, &swapInfo, 1);
        usleep(40000);
        g.mouseMoved[0] = 0;
        g.mouseMoved[1] = 0;
    }
    cleanupXwindows();
    return 0;
}

void cleanupXwindows(void)
{
    if(!XdbeDeallocateBackBufferName(dpy, backBuffer))
    {
        fprintf(stderr, "Error : unable to deallocate back buffer.\n");
    }
    XFreeGC(dpy, gc);
    XDestroyWindow(dpy, win);
    XCloseDisplay(dpy);
}

void initXwindows(void)
{
    XSetWindowAttributes attributes;
    int major, minor;
    XdbeBackBufferAttributes *backAttr;

    dpy = XOpenDisplay(NULL);
    //List of events we want to handle
    attributes.event_mask = ExposureMask | StructureNotifyMask |
        PointerMotionMask | ButtonPressMask |
        ButtonReleaseMask | KeyPressMask;
    //Various window attributes
    attributes.backing_store = Always;
    attributes.save_under = True;
    attributes.override_redirect = False;
    attributes.background_pixel = 0x00000000;
    //Get default root window
    Window root = DefaultRootWindow(dpy);
    //Create a window
    win = XCreateWindow(dpy, root, 0, 0, g.xres, g.yres, 0,
            CopyFromParent, InputOutput, CopyFromParent,
            CWBackingStore | CWOverrideRedirect | CWEventMask |
            CWSaveUnder | CWBackPixel, &attributes);
    //Create gc
    gc = XCreateGC(dpy, win, 0, NULL);
    //Get DBE version
    if (!XdbeQueryExtension(dpy, &major, &minor)) {
        fprintf(stderr, "Error : unable to fetch Xdbe Version.\n");
        XFreeGC(dpy, gc);
        XDestroyWindow(dpy, win);
        XCloseDisplay(dpy);
        exit(1);
    }
    printf("Xdbe version %d.%d\n",major,minor);
    //Get back buffer and attributes (used for swapping)
    backBuffer = XdbeAllocateBackBufferName(dpy, win, XdbeUndefined);
    backAttr = XdbeGetBackBufferAttributes(dpy, backBuffer);
    swapInfo.swap_window = backAttr->window;
    swapInfo.swap_action = XdbeUndefined;
    XFree(backAttr);
    //Map and raise window
    XMapWindow(dpy, win);
    XRaiseWindow(dpy, win);
    //setWindowTitle();
}


void checkResize(XEvent *e)
{
    //ConfigureNotify is sent when window size changes.
    if (e->type != ConfigureNotify)
        return;
    XConfigureEvent xce = e->xconfigure;
    g.xres = xce.width;
    g.yres = xce.height;
    initGrid();
}

void clearScreen(void)
{
    //XClearWindow(dpy, backBuffer);
    XSetForeground(dpy, gc, 0x00000000);
    XFillRectangle(dpy, backBuffer, gc, 0, 0, g.xres, g.yres);
}

void checkMouse(XEvent *e)
{
    static int savex = 0;
    static int savey = 0;
    int mx = e->xbutton.x;
    int my = e->xbutton.y;
    //
    if (e->type == ButtonRelease) {
        return;
    }
    if (e->type == ButtonPress) {
        //Log("ButtonPress %i %i\n", e->xbutton.x, e->xbutton.y);
        if (e->xbutton.button==1) {
            //Left button pressed
        }
        if (e->xbutton.button==3) {
            //Right button pressed
        }
    }
    if (savex != mx || savey != my) {
        //mouse moved
        g.mouseMoved[0] = e->xbutton.x - savex;
        g.mouseMoved[1] = e->xbutton.y - savey;
        savex = e->xbutton.x;
        savey = e->xbutton.y;
        g.lastMouse[0] = savex;
        g.lastMouse[1] = savey;
        g.mouseGrid[0] = savex/g.grid.size;
        g.mouseGrid[1] = savey/g.grid.size;
    }
    else
    {
        g.mouseMoved[0] = 0;
        g.mouseMoved[1] = 0;
    }
}


void checkKeys(XEvent *e)
{
    if (e->type != KeyPress)
        return;
    //A key was pressed
    int key = XLookupKeysym(&e->xkey, 0);
    switch (key) {
        case XK_Escape:
            //quitting the program
            g.done=1;
            break;

        case XK_b:
            g.bubbler ^= 1;
            break;

        case XK_g:
            g.drawGrid ^= 1;
            initGrid();
            break;

        case XK_c:
            g.control ^= 1;
            break;

        case XK_f:
            g.fluid ^= 1;
            break;

        case XK_1:
            visc -= 1.0;
            break;
        case XK_2:
            visc += 1.0;
            break;

        case XK_3:
            dt -= 1.0;
            break;
        case XK_4:
            dt += 1.0;
            break;

        case XK_5:
            diff -= 1.0;
            break;
        case XK_6:
            diff += 1.0;
            break;
    }
    clearScreen();
}

void physics(Global *g)
{
    if(g->bubbler && g->control)
        dens_prev[IX(g->mouseGrid[0], g->mouseGrid[1])] += 1.0;
    if(g->bubbler && !g->control)
        dens_prev[IX((int)(g->xres/2/g->grid.size), (int)(2*g->yres)/3/g->grid.size)] += 1.0;
}

void setColor3i(int r, int g, int b)
{
    unsigned long cref = 0L;
    cref += r;
    cref <<= 8;
    cref += g;
    cref <<= 8;
    cref += b;
    XSetForeground(dpy, gc, cref);
}

void showMenu(int x, int y, const char *message)
{
    char ts[64];

    setColor3i(100, 255, 255);
    sprintf(ts,"Jason Thai");
    XDrawString(dpy, backBuffer, gc, x, y, ts, strlen(ts));

    y += 16;
    sprintf(ts,"CMPS-3480 : Project - Fire");
    XDrawString(dpy, backBuffer, gc, x, y, ts, strlen(ts));

    y += 32;
    setColor3i(255,255,255);
    XDrawString(dpy, backBuffer, gc, x, y, message, strlen(message));
    y += 16;
    sprintf(ts,"1-2 : Decrease/Increase viscosity");
    XDrawString(dpy, backBuffer, gc, x, y, ts, strlen(ts));
    y += 16;
    sprintf(ts,"3-4 : Decrease/Increase time spacing");
    XDrawString(dpy, backBuffer, gc, x, y, ts, strlen(ts));
    y += 16;
    sprintf(ts,"5-6 : Decrease/Increase rate of diffusion");
    XDrawString(dpy, backBuffer, gc, x, y, ts, strlen(ts));
    //
    y += 32;
    sprintf(ts,"Viscosity: %f", visc);
    XDrawString(dpy, backBuffer, gc, x, y, ts, strlen(ts));
    y += 16;
    sprintf(ts,"Time spacing: %f", dt);
    XDrawString(dpy, backBuffer, gc, x, y, ts, strlen(ts));
    y += 16;
    sprintf(ts,"Rate of diffusion: %f", diff);
    XDrawString(dpy, backBuffer, gc, x, y, ts, strlen(ts));
    //
    y += 32;
    (g.bubbler==1) ? setColor3i(0,255,0) : setColor3i(255,0,0);
    sprintf(ts,"(B) Bubbler: %s", (g.bubbler==1)?"ON":"OFF");
    XDrawString(dpy, backBuffer, gc, x, y, ts, strlen(ts));

    y += 16;
    (g.drawGrid==1) ? setColor3i(0,255,0) : setColor3i(255,0,0);
    sprintf(ts,"(G) Grid/Reset: %s", (g.drawGrid==1)?"ON":"OFF");
    XDrawString(dpy, backBuffer, gc, x, y, ts, strlen(ts));

    y += 16;
    (g.control==1) ? setColor3i(0,255,0) : setColor3i(255,0,0);
    sprintf(ts,"(C) Control fire: %s", (g.control==1)?"ON":"OFF");
    XDrawString(dpy, backBuffer, gc, x, y, ts, strlen(ts));
    
    y += 16;
    (g.fluid==1) ? setColor3i(0,255,0) : setColor3i(255,0,0);
    sprintf(ts,"(F) Fluid: %s", (g.fluid==1)?"ON":"OFF");
    XDrawString(dpy, backBuffer, gc, x, y, ts, strlen(ts));
}

void render(void)
{
    for(int i = 0; i < N; i++)
    {
        for(int j = 0; j < N; j++)
        {
            if(!g.fluid)
            {
                if(dens[IX(i,j)]*100 >= 1.0)
                    setColor3i(255,0,0);
                else if(dens[IX(i,j)]*100 >= 0.8)
                    setColor3i(255*dens[IX(i,j)]*100, 50*dens[IX(i,j)]*100, 0);
                else if(dens[IX(i,j)]*100 >= 0.6)
                    setColor3i(255*dens[IX(i,j)]*100, 100*dens[IX(i,j)]*100, 0);
                else if(dens[IX(i,j)]*100 >= 0.4)
                    setColor3i(255*dens[IX(i,j)]*100, 165*dens[IX(i,j)]*100, 0);
                else if(dens[IX(i,j)]*100 >= 0.2)
                    setColor3i(255*dens[IX(i,j)]*100, 225*dens[IX(i,j)]*100, 0);
                else
                    setColor3i(255*dens[IX(i,j)]*100, 255*dens[IX(i,j)]*100, 0);
            }
            else if(g.fluid)
            {
                if(dens_prev[IX(i,j)]*100 >= 1.0)
                    setColor3i(255,0,0);
                else if(dens_prev[IX(i,j)]*100 >= 0.8)
                    setColor3i(255*dens_prev[IX(i,j)]*100, 50*dens_prev[IX(i,j)]*100, 0);
                else if(dens_prev[IX(i,j)]*100 >= 0.6)
                    setColor3i(255*dens_prev[IX(i,j)]*100, 100*dens_prev[IX(i,j)]*100, 0);
                else if(dens_prev[IX(i,j)]*100 >= 0.4)
                    setColor3i(255*dens_prev[IX(i,j)]*100, 165*dens_prev[IX(i,j)]*100, 0);
                else if(dens_prev[IX(i,j)]*100 >= 0.2)
                    setColor3i(255*dens_prev[IX(i,j)]*100, 225*dens_prev[IX(i,j)]*100, 0);
                else
                    setColor3i(255*dens_prev[IX(i,j)]*100, 255*dens_prev[IX(i,j)]*100, 0);
            }

            XFillRectangle(dpy, backBuffer, gc, g.grid.column[i], g.grid.row[j], 10, 10);
        }
    }

    if(g.drawGrid)
    {
        setColor3i(255,255,255);
        for(size_t i = 0; i < sizeof(g.grid.column)/4; i++)
            XDrawLine(dpy, backBuffer, gc, g.grid.column[i], 0, g.grid.column[i], g.yres);
        for(size_t i = 0; i < sizeof(g.grid.row)/4; i++)
            XDrawLine(dpy, backBuffer, gc, 0, g.grid.row[i], g.xres, g.grid.row[i]);
    }

    showMenu(4, 16, "Press key:");
}


void initGrid()
{
    g.grid.size = 10;

    int position = 0;
    for(int i = 0; i < g.xres; i += g.grid.size)
    {
        g.grid.column[position] = i;
        position++;
    }
    position = 0;
    for(int i = 0; i < g.yres; i += g.grid.size)
    {
        g.grid.row[position] = i;
        position++;
    }
    for(int i = 0; i < size; i++)
    {
        dens_prev[i] = 0.0;
        u_prev[i] = 0.0;
        v_prev[i] = 0.0;
    }
}

void checkGrid(Global *g)
{
    for(int i = 0; i < size; i++)
    {
        u_prev[i] = rand() % 3 - 1;
        v_prev[i] = rand() % 3 - 1;
    }
}
