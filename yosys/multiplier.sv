// Designed by Michalis Pardalos
// Modified by John Wickerson

module multiplier (
    input rst,
    input clk,
    input [7:0] in1,
    input [7:0] in2,
    output [15:0] out
);
    reg [3:0]  stage = 0;
    reg [15:0] accumulator = 0;
    reg [7:0]  in1_shifted = 0;
    reg [15:0] in2_shifted = 0;


    // Logic for controlling the stage
    always @(posedge clk)
        if (rst || stage == 9)
            stage <= 0;
        else
            stage <= stage + 1;

    // Logic for in1_shifted and in2_shifted
    always @(posedge clk)
        if (rst) begin
            in1_shifted <= 0;
            in2_shifted <= 0;
        end else if (stage == 0) begin
            in1_shifted <= in1;
            in2_shifted <= in2;
        end else begin
            in1_shifted <= in1_shifted >> 1;
            in2_shifted <= in2_shifted << 1;
        end

    // Logic for the accumulator
    always @(posedge clk)
        if (rst || stage == 9) begin
            accumulator <= 0;
        end else if (in1_shifted[0]) begin
            accumulator <= accumulator + in2_shifted;
        end

    // Output logic
    assign out = accumulator;


`ifdef FORMAL
    reg [7:0] in1_init;
    reg [7:0] in2_init;

    always @(posedge clk) begin
        // just to grab the initial values of in1 and in2
        if (rst) begin
            in1_init <= 0;
            in2_init <= 0;
        end else if (stage == 0) begin
            in1_init <= in1;
            in2_init <= in2;
        end
    end

    /* mode=prove depth=12
    Justifying depth of 12 by the fact that multiplication only lasts 9 stages,
    I'm only passing a couple other cycles for safety, but more is unnecessary
    Also during testing, all counter-examples came before step 11, never after
    */

    /** SWI: Stage Wraparound Invalidity (stage 0 and 9 edge cases)
        Because in1 and in2 are 8-bit numbers, stage only has meaning up to 9.
        Stage 0 is just an initial stage, where registers are being loaded.
        Once all 8 bits of in1 have been shifted out, the computation is done.
        Wraparound to 0 doesn't affect validity of the multiplication, because:
            - at 0, all registers are reset, and the multiplication starts again
            - 0 can also be reached by `rst`, which is a valid consideration,
              however, it doesn't affect the validity of the multiplication
        The multiplication is simply the process from stages 1 to 9, and thus
        these following properties need only be ensured from stage 1 onwards

        The only thing we need to ensure between stage 9 and stage 0,
        is that the wraparound is logically correct, i.e. that everything is
        reset as expected, and that the multiplication is correct up to stage 9
    */

    always @(*) begin
        // question 1: upper bound on the output (255*255)
        assert (out <= 16'b1111111000000001);

        // just for fun
        assert ((stage < 10) && (stage >= 0));
    end

    always @(posedge clk) begin
        // question 2: stage increments (mod 10), so long as rst is low
        assert property (
            1 |=> ($past(rst) || (stage == (($past(stage) + 1) % 10)))
        );
        /*
        - `1 |=>` to skip first cycle
        - check for `$past(rst)`, cos rst will hold stage at 0
        - last cond. checks stage inc., `%10` cos stage == 9 before it resets
        */

        // question 3: main property
        assert property ((stage < 9) || (out == in1_init * in2_init));
        /*
        - sth
        */

        // question 4: monotonic increase of output
        assert property (
            stage == 0 || out >= $past(out)
        );
        /*
        - very simply, from stage 0 onwards, the output will:
          - increase - calculation ongoing
          - stay the same - calculation finished before stage 9
        */

        // because rst restarts the multiplication which we're interested in
        if (!rst) begin
            // question 5: at stage 4
            assert property (
                (stage == 4) |=>
                    (out == (in2_init * (in1_init & 8'b1111)))
            );
            /*
            - I use a bitmask to get the last 4 bits of in1
            */

            // question 6: q5 at every other stage
            assert property (
                (stage == 0) |=> (out == (in2_init * (in1_init & 8'b0)))
            );
            assert property (
                (stage == 1) |=> (out == (in2_init * (in1_init & 8'b1)))
            );
            assert property (
                (stage == 2) |=> (out == (in2_init * (in1_init & 8'b11)))
            );
            assert property (
                (stage == 3) |=> (out == (in2_init * (in1_init & 8'b111)))
            );
            assert property (
                (stage == 5) |=> (out == (in2_init * (in1_init & 8'b11111)))
            );
            assert property (
                (stage == 6) |=> (out == (in2_init * (in1_init & 8'b111111)))
            );
            assert property (
                (stage == 7) |=> (out == (in2_init * (in1_init & 8'b1111111)))
            );
            assert property (
                (stage == 8) |=> (out == (in2_init * (in1_init & 8'b11111111)))
            );
            assert property (
                (stage == 9) |=> (out == 0)
            );
            // by SWI, stage 9 is weird, as 8 is the last computation stage,
            // and because `stage 9 |=>` is stage 0, where everything is reset
            /*
            - same as q5, I just used a bitmask to get the LS{stage}B of in1
            */
        end


        // Q7 Prove that in1_shifted always holds the initial value of in1, shifted right by stage bits
        assert property (
            ((in1_shifted) == (in1_init >> stage-1))
        )
        $error("Q7 does not hold");

        // Q8 Prove that in2_shifted always holds the initial value of in2, shifted left by stage bits, provided stage has not reset
        assert property (
            ((in2_shifted) == (in2_init << stage-1)) || stage == 0
        )
        $error("Q8 does not hold");

        // question 9: 13 is prime (cover was taking too long to run)
        cover(
            (stage == 9) && (out == 13) && (in1_init != 13) && (in2_init != 13)
        );
        /*
        - any two numbers (excluding 13) multiplied together shouldn't yield 13
          - definition of a prime number
        - at stage 9 (at end of calc)
          - if the output is 13 => an input must have been 13
        */

        // question 10: q5 and q6 in one concise statement
        assert property (
            1 |=> (
                out == ($past(stage) == 9 ? 0 :
                    (in2_init * (in1_init & (2**$past(stage) - 1)))
                )
            )
        );
        /*
        - because 2**n - 1 = 1111...1, where there are n 1s
          this is equivalent to the bitmasks I was applying above
        - using SWI again, because out == 0 after stage 9
        */
    end

`endif


endmodule
